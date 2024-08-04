using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie
{
  public class AtomicActionLiveVariableAnalysis
  {
    private Implementation impl;
    private ConcurrencyOptions options;
    private Dictionary<Block, HashSet<Variable>> liveVarsBefore;
    private Dictionary<Cmd, HashSet<Variable>> liveVarsAfter;

    public AtomicActionLiveVariableAnalysis(Implementation impl, ConcurrencyOptions options)
    {
      this.impl = impl;
      this.options = options;
      this.liveVarsBefore = new Dictionary<Block, HashSet<Variable>>();
      this.liveVarsAfter = new Dictionary<Cmd, HashSet<Variable>>();
    }

    public void Compute()
    {
      var graph = Program.GraphFromImpl(impl, false);
      foreach (var block in graph.TopologicalSort())
      {
        if (block.TransferCmd is ReturnCmd)
        {
          liveVarsBefore[block] = Propagate(block.Cmds,
            impl.Proc.Modifies.Select(x => x.Decl).Concat(impl.OutParams).ToHashSet());
        }
        else if (block.TransferCmd is GotoCmd gotoCmd)
        {
          liveVarsBefore[block] =
            Propagate(block.Cmds, gotoCmd.labelTargets.SelectMany(x => liveVarsBefore[x]).ToHashSet());
        }
        else
        {
          throw new Cce.UnreachableException();
        }
      }
    }

    public bool IsLiveAfter(Variable v, Cmd cmd)
    {
      return liveVarsAfter[cmd].Contains(v);
    }

    public bool IsLiveBefore(Variable v, Block block)
    {
      return liveVarsBefore[block].Contains(v);
    }

    private HashSet<Variable> Propagate(List<Cmd> cmds, HashSet<Variable> liveVars)
    {
      for (int i = cmds.Count - 1; i >= 0; i--)
      {
        var cmd = cmds[i];
        liveVarsAfter[cmd] = new HashSet<Variable>(liveVars);
        liveVars = Propagate(cmd, liveVars);
      }
      return liveVars;
    }

    private HashSet<Variable> Propagate(Cmd cmd, HashSet<Variable> liveVars)
    {
      if (cmd is HavocCmd havocCmd)
      {
        liveVars.ExceptWith(havocCmd.Vars.Select(v => v.Decl));
        return liveVars;
      }
      if (cmd is AssignCmd assignCmd)
      {
        var usedVars = new HashSet<Variable>();
        for (int i = 0; i < assignCmd.Lhss.Count; i++)
        {
          var lhs = assignCmd.Lhss[i];
          var rhs = assignCmd.Rhss[i];
          if (liveVars.Contains(lhs.DeepAssignedVariable))
          {
            liveVars.Remove(lhs.DeepAssignedVariable);
            var variableCollector = new VariableCollector();
            variableCollector.VisitExpr(rhs);
            usedVars.UnionWith(variableCollector.usedVars);
          }
        }
        liveVars.UnionWith(usedVars);
        return liveVars;
      }
      if (cmd is PredicateCmd predicateCmd)
      {
        var variableCollector = new VariableCollector();
        variableCollector.VisitExpr(predicateCmd.Expr);
        liveVars.UnionWith(variableCollector.usedVars);
        return liveVars;
      }
      if (cmd is SugaredCmd sugaredCmd)
      {
        return Propagate(sugaredCmd.GetDesugaring(options), liveVars);
      }
      if (cmd is CommentCmd)
      {
        return liveVars;
      }
      if (cmd is StateCmd stateCmd)
      {
        liveVars = Propagate(stateCmd.Cmds, liveVars);
        liveVars.ExceptWith(stateCmd.Locals);
        return liveVars;
      }
      throw new Cce.UnreachableException();
    }
  }

  public class CivlUtil
  {
    public static void AddInlineAttribute(Declaration decl)
    {
      decl.AddAttribute("inline", Expr.Literal(1));
    }

    public static int ResolveAndTypecheck(CoreOptions options, Absy absy, ResolutionContext.State state = ResolutionContext.State.Single)
    {
      var rc = new ResolutionContext(null, options);
      if (state == ResolutionContext.State.Two)
      {
        rc.StateMode = state;
      }
      absy.Resolve(rc);
      if (rc.ErrorCount != 0)
      {
        return rc.ErrorCount;
      }

      var tc = new TypecheckingContext(null, options);
      tc.CheckModifies = false; // to prevent access to tc.Proc which is null
      absy.Typecheck(tc);
      return tc.ErrorCount;
    }

    public static int ResolveAndTypecheck(CoreOptions options, IEnumerable<Absy> absys, ResolutionContext.State state = ResolutionContext.State.Single)
    {
      int errorCount = 0;
      foreach (var absy in absys)
      {
        errorCount += ResolveAndTypecheck(options, absy, state);
      }
      return errorCount;
    }
  }

  // Handy syntactic sugar missing in Expr
  public static class ExprHelper
  {
    public static NAryExpr FunctionCall(Function f, List<Expr> args)
    {
      return new NAryExpr(Token.NoToken, new FunctionCall(f), args);
    }

    public static NAryExpr FunctionCall(IAppliable f, params Expr[] args)
    {
      return new NAryExpr(Token.NoToken, f, args);
    }

    public static NAryExpr FunctionCall(Function f, params Expr[] args)
    {
      return new NAryExpr(Token.NoToken, new FunctionCall(f), args);
    }
    
    public static NAryExpr FieldAccess(Expr path, string fieldName)
    {
      return new NAryExpr(Token.NoToken, new FieldAccess(Token.NoToken, fieldName), new Expr[] { path });
    }

    public static NAryExpr IsConstructor(Expr path, string constructorName)
    {
      return new NAryExpr(Token.NoToken, new IsConstructor(Token.NoToken, constructorName), new Expr[] { path });
    }
    
    public static NAryExpr IfThenElse(Expr ifExpr, Expr thenExpr, Expr elseExpr)
    {
      return new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken),
        new Expr[] {ifExpr, thenExpr, elseExpr});
    }

    public static OldExpr Old(Expr expr)
    {
      return new OldExpr(Token.NoToken, expr);
    }

    public static ExistsExpr ExistsExpr(List<Variable> dummies, Expr body)
    {
      return new ExistsExpr(Token.NoToken, dummies, body);
    }

    public static ExistsExpr ExistsExpr(List<Variable> dummies, Trigger triggers, Expr body)
    {
      return new ExistsExpr(Token.NoToken, dummies, triggers, body);
    }

    public static ForallExpr ForallExpr(List<Variable> dummies, Expr body)
    {
      return new ForallExpr(Token.NoToken, dummies, body);
    }

    public static void FlattenAnd(Expr x, List<Expr> xs)
    {
      if (x is NAryExpr naryExpr && naryExpr.Fun.FunctionName == "&&")
      {
        FlattenAnd(naryExpr.Args[0], xs);
        FlattenAnd(naryExpr.Args[1], xs);
      }
      else
      {
        xs.Add(x);
      }
    }
  }

  public static class CmdHelper
  {
    public static ReturnCmd ReturnCmd => new ReturnCmd(Token.NoToken);

    public static CallCmd CallCmd(Procedure callee, List<Expr> ins, List<IdentifierExpr> outs)
    {
      return new CallCmd(Token.NoToken, callee.Name, ins, outs)
        { Proc = callee };
    }

    public static CallCmd CallCmd(Procedure callee, List<Variable> ins, List<Variable> outs)
    {
      return CallCmd(callee, ins.Select(Expr.Ident).ToList<Expr>(), outs.Select(Expr.Ident).ToList());
    }

    public static AssumeCmd AssumeCmd(Expr expr)
    {
      return new AssumeCmd(Token.NoToken, expr);
    }

    public static AssertCmd AssertCmd(IToken tok, Expr expr, string msg)
    {
      return new AssertCmd(tok, expr)
        { Description = new FailureOnlyDescription(msg) };
    }

    public static SimpleAssignLhs SimpleAssignLhs(Variable v)
    {
      return new SimpleAssignLhs(Token.NoToken, Expr.Ident(v));
    }

    public static FieldAssignLhs FieldAssignLhs(AssignLhs path, string fieldName)
    {
      return new FieldAssignLhs(Token.NoToken, path, new FieldAccess(Token.NoToken, fieldName));
    }
    
    public static FieldAssignLhs FieldAssignLhs(Expr path, string fieldName)
    {
      return new FieldAssignLhs(Token.NoToken, ExprToAssignLhs(path), new FieldAccess(Token.NoToken, fieldName));
    }
    
    public static AssignLhs ExprToAssignLhs(Expr e)
    {
      if (e is IdentifierExpr ie)
      {
        return SimpleAssignLhs(ie.Decl);
      }
      var naryExpr = (NAryExpr)e;
      if (naryExpr.Fun is FieldAccess fieldAccess)
      {
        return FieldAssignLhs(naryExpr.Args[0], fieldAccess.FieldName);
      }
      if (naryExpr.Fun is MapSelect)
      {
        return new MapAssignLhs(Token.NoToken, ExprToAssignLhs(naryExpr.Args[0]), naryExpr.Args.ToList().GetRange(1, naryExpr.Args.Count - 1));
      }
      Contract.Assume(false, "Unexpected expression");
      return null;
    }
    
    public static AssignCmd AssignCmd(Variable v, Expr x)
    {
      var lhs = SimpleAssignLhs(v);
      return new AssignCmd(Token.NoToken, new List<AssignLhs> {lhs}, new List<Expr> {x});
    }

    public static AssignCmd AssignCmd(AssignLhs lhs, Expr x)
    {
      return new AssignCmd(Token.NoToken, new List<AssignLhs> {lhs}, new List<Expr> {x});
    }

    public static AssignCmd AssignCmd(IList<IdentifierExpr> lhss, IList<Expr> rhss)
    {
      var assignLhss = lhss.Select(lhs => new SimpleAssignLhs(Token.NoToken, lhs)).ToList<AssignLhs>();
      return new AssignCmd(Token.NoToken, assignLhss, rhss);
    }

    public static HavocCmd HavocCmd(List<IdentifierExpr> vars)
    {
      return new HavocCmd(Token.NoToken, vars);
    }

    public static HavocCmd HavocCmd(params IdentifierExpr[] vars)
    {
      return new HavocCmd(Token.NoToken, vars.ToList());
    }
  }

  public static class BlockHelper
  {
    public static Block Block(string label, List<Cmd> cmds)
    {
      return new Block(Token.NoToken, label, cmds, CmdHelper.ReturnCmd);
    }

    public static Block Block(string label, List<Cmd> cmds, List<Block> gotoTargets)
    {
      return new Block(Token.NoToken, label, cmds, new GotoCmd(Token.NoToken, gotoTargets));
    }
  }

  public static class DeclHelper
  {
    public static Procedure Procedure(string name,
      List<Variable> inParams, List<Variable> outParams,
      List<Requires> requires, List<IdentifierExpr> modifies, List<Ensures> ensures,
      QKeyValue kv = null)
    {
      return new Procedure(Token.NoToken, name, new List<TypeVariable>(), inParams, outParams, false, requires, modifies, ensures, kv);
    }

    public static Implementation Implementation(Procedure proc,
      List<Variable> inParams, List<Variable> outParams, List<Variable> localVariables,
      List<Block> blocks, QKeyValue kv = null)
    {
      return new Implementation(Token.NoToken, proc.Name, new List<TypeVariable>(), inParams, outParams, localVariables, blocks, kv) { Proc = proc };
    }
  }

  public static class VarHelper
  {
    public static LocalVariable LocalVariable(string name, Type type)
    {
      return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
    }

    public static BoundVariable BoundVariable(string name, Type type)
    {
      return new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
    }

    public static Formal Formal(string name, Type type, bool incoming)
    {
      return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, name, type), incoming);
    }
  }

  public static class TypeHelper
  {
    public static MapType MapType(Type indexType, Type resultType)
    {
      return new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { indexType }, resultType);
    }

    public static CtorType CtorType(TypeCtorDecl typeCtorDecl)
    {
      return new CtorType(Token.NoToken, typeCtorDecl, new List<Type>());
    }
  }
  
  public static class SubstitutionHelper
  {
    public static Substitution FromVariableMap(Dictionary<Variable, Variable> map)
    {
      return Substituter.SubstitutionFromDictionary(map.ToDictionary(kv => kv.Key, kv => (Expr) Expr.Ident(kv.Value)));
    }

    public static Expr Apply(Dictionary<Variable, Expr> map, Expr expr)
    {
      return Substituter.Apply(Substituter.SubstitutionFromDictionary(map), expr);
    }

    public static Expr Apply(Dictionary<Variable, Variable> map, Expr expr)
    {
      return Substituter.Apply(FromVariableMap(map), expr);
    }

    public static Cmd Apply(Dictionary<Variable, Expr> map, Cmd cmd)
    {
      return Substituter.Apply(Substituter.SubstitutionFromDictionary(map), cmd);
    }

    public static Cmd Apply(Dictionary<Variable, Variable> map, Cmd cmd)
    {
      return Substituter.Apply(FromVariableMap(map), cmd);
    }

    public static IEnumerable<Expr> Apply(Substitution subst, IEnumerable<Expr> exprs)
    {
      return exprs.Select(x => Substituter.Apply(subst, x));
    }

    public static IEnumerable<Expr> Apply(Dictionary<Variable, Expr> map, IEnumerable<Expr> exprs)
    {
      var subst = Substituter.SubstitutionFromDictionary(map);
      return Apply(subst, exprs);
    }

    public static IEnumerable<Expr> Apply(Dictionary<Variable, Variable> map, IEnumerable<Expr> exprs)
    {
      var subst = FromVariableMap(map);
      return Apply(subst, exprs);
    }

    public static IEnumerable<Cmd> Apply(Substitution subst, IEnumerable<Cmd> cmds)
    {
      return cmds.Select(x => Substituter.Apply(subst, x));
    }

    public static IEnumerable<Cmd> Apply(Dictionary<Variable, Expr> map, IEnumerable<Cmd> cmds)
    {
      var subst = Substituter.SubstitutionFromDictionary(map);
      return Apply(subst, cmds);
    }

    public static IEnumerable<Cmd> Apply(Dictionary<Variable, Variable> map, IEnumerable<Cmd> cmds)
    {
      var subst = FromVariableMap(map);
      return Apply(subst, cmds);
    }
  }

  public static class LinqExtensions
  {
    public static IEnumerable<IEnumerable<T>> CartesianProduct<T>(this IEnumerable<IEnumerable<T>> sequences)
    {
      IEnumerable<IEnumerable<T>> emptyProduct = new[] {Enumerable.Empty<T>()};
      return sequences.Aggregate(
        emptyProduct,
        (accumulator, sequence) =>
          from acc in accumulator
          from item in sequence
          select acc.Concat(new[] {item}));
    }
  }
}