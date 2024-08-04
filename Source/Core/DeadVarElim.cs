using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public class UnusedVarEliminator : VariableCollector
  {
    public static void Eliminate(Program program)
    {
      Contract.Requires(program != null);
      UnusedVarEliminator elim = new UnusedVarEliminator();
      elim.Visit(program);
    }

    private UnusedVarEliminator()
      : base()
    {
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      //Console.WriteLine("Procedure {0}", node.Name);
      Implementation /*!*/
        impl = base.VisitImplementation(node);
      Contract.Assert(impl != null);
      //Console.WriteLine("Old number of local variables = {0}", impl.LocVars.Length);
      List<Variable> /*!*/
        vars = new List<Variable>();
      foreach (Variable /*!*/ var in impl.LocVars)
      {
        Contract.Assert(var != null);
        if (_usedVars.Contains(var))
        {
          vars.Add(var);
        }
      }

      impl.LocVars = vars;
      //Console.WriteLine("New number of local variables = {0}", impl.LocVars.Length);
      //Console.WriteLine("---------------------------------");
      _usedVars.Clear();
      return impl;
    }
  }

  public class ModSetCollector : ReadOnlyVisitor
  {
    private CoreOptions options;
    private Procedure enclosingProc;

    private Dictionary<Procedure, HashSet<Variable>> modSets;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullDictionaryAndValues(modSets));
      Contract.Invariant(Contract.ForAll(modSets.Values, v => Cce.NonNullElements(v)));
    }

    public ModSetCollector(CoreOptions options)
    {
      this.options = options;
      modSets = new Dictionary<Procedure, HashSet<Variable>>();
    }

    private bool moreProcessingRequired;

    public void DoModSetAnalysis(Program program)
    {
      Contract.Requires(program != null);

      if (options.Trace)
      {
//          Console.WriteLine();
//          Console.WriteLine("Running modset analysis ...");
//          int procCount = 0;
//          foreach (Declaration/*!*/ decl in program.TopLevelDeclarations)
//          {
//              Contract.Assert(decl != null);
//              if (decl is Procedure)
//                  procCount++;
//          }
//          Console.WriteLine("Number of procedures = {0}", procCount);*/
      }

      HashSet<Procedure /*!*/> implementedProcs = new HashSet<Procedure /*!*/>();
      foreach (var impl in program.Implementations)
      {
        if (impl.Proc != null)
        {
          implementedProcs.Add(impl.Proc);
        }
      }

      foreach (var proc in program.Procedures)
      {
        if (!implementedProcs.Contains(proc))
        {
          enclosingProc = proc;
          foreach (var expr in proc.Modifies)
          {
            Contract.Assert(expr != null);
            ProcessVariable(expr.Decl);
          }

          enclosingProc = null;
        }
        else
        {
          modSets.Add(proc, new HashSet<Variable>());
        }
      }

      moreProcessingRequired = true;
      while (moreProcessingRequired)
      {
        moreProcessingRequired = false;
        this.Visit(program);
      }

      foreach (Procedure x in modSets.Keys)
      {
        x.Modifies = new List<IdentifierExpr>();
        foreach (Variable v in modSets[x])
        {
          x.Modifies.Add(new IdentifierExpr(v.tok, v));
        }
      }

#if DEBUG_PRINT
      options.OutputWriter.WriteLine("Number of procedures with nonempty modsets = {0}", modSets.Keys.Count);
      foreach (Procedure/*!*/ x in modSets.Keys) {
        Contract.Assert(x != null);
        options.OutputWriter.Write("{0} : ", x.Name);
        bool first = true;
        foreach (Variable/*!*/ y in modSets[x]) {
          Contract.Assert(y != null);
          if (first)
            first = false;
          else
            options.OutputWriter.Write(", ");
          options.OutputWriter.Write("{0}", y.Name);
        }
        options.OutputWriter.WriteLine("");
      options.OutputWriter
#endif
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      enclosingProc = node.Proc;
      Implementation /*!*/
        ret = base.VisitImplementation(node);
      Contract.Assert(ret != null);
      enclosingProc = null;

      return ret;
    }

    public override Cmd VisitAssignCmd(AssignCmd assignCmd)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Cmd ret = base.VisitAssignCmd(assignCmd);
      foreach (AssignLhs lhs in assignCmd.Lhss)
      {
        Contract.Assert(lhs != null);
        ProcessVariable(lhs.DeepAssignedVariable);
      }

      return ret;
    }

    public override Cmd VisitUnpackCmd(UnpackCmd unpackCmd)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Cmd ret = base.VisitUnpackCmd(unpackCmd);
      foreach (var expr in unpackCmd.Lhs.Args)
      {
        ProcessVariable(((IdentifierExpr)expr).Decl);
      }
      return ret;
    }
    
    public override Cmd VisitHavocCmd(HavocCmd havocCmd)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Cmd ret = base.VisitHavocCmd(havocCmd);
      foreach (IdentifierExpr expr in havocCmd.Vars)
      {
        Contract.Assert(expr != null);
        ProcessVariable(expr.Decl);
      }

      return ret;
    }

    public override Cmd VisitCallCmd(CallCmd callCmd)
    {
      //Contract.Requires(callCmd != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Cmd ret = base.VisitCallCmd(callCmd);
      foreach (IdentifierExpr ie in callCmd.Outs)
      {
        if (ie != null)
        {
          ProcessVariable(ie.Decl);
        }
      }

      Procedure callee = callCmd.Proc;
      if (callee == null)
      {
        return ret;
      }

      if (modSets.ContainsKey(callee))
      {
        foreach (Variable var in modSets[callee])
        {
          ProcessVariable(var);
        }
      }

      return ret;
    }

    private void ProcessVariable(Variable var)
    {
      Procedure /*!*/
        localProc = Cce.NonNull(enclosingProc);
      if (var == null)
      {
        return;
      }

      if (!(var is GlobalVariable))
      {
        return;
      }

      if (!modSets.ContainsKey(localProc))
      {
        modSets[localProc] = new HashSet<Variable /*!*/>();
      }

      if (modSets[localProc].Contains(var))
      {
        return;
      }

      moreProcessingRequired = true;
      modSets[localProc].Add(var);
    }

    public override Expr VisitCodeExpr(CodeExpr node)
    {
      // don't go into the code expression, since it can only modify variables local to the code expression,
      // and the mod-set analysis is interested in global variables
      return node;
    }
  }

  public class MutableVariableCollector : ReadOnlyVisitor
  {
    public HashSet<Variable> UsedVariables = new HashSet<Variable>();

    public void AddUsedVariables(HashSet<Variable> usedVariables)
    {
      Contract.Requires(usedVariables != null);

      foreach (var v in usedVariables)
      {
        UsedVariables.Add(v);
      }
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() != null);

      if (node.Decl != null && node.Decl.IsMutable)
      {
        UsedVariables.Add(node.Decl);
      }

      return base.VisitIdentifierExpr(node);
    }
  }

  public class VariableCollector : ReadOnlyVisitor
  {
    private bool _ignoreOld;

    protected HashSet<Variable> _usedVars;

    public IEnumerable<Variable> usedVars
    {
      get { return _usedVars.AsEnumerable(); }
    }

    protected HashSet<Variable> _oldVarsUsed;

    public IEnumerable<Variable> oldVarsUsed
    {
      get { return _oldVarsUsed.AsEnumerable(); }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(_usedVars));
      Contract.Invariant(Cce.NonNullElements(_oldVarsUsed));
    }

    int insideOldExpr;

    public VariableCollector(bool ignoreOld = false)
    {
      _ignoreOld = ignoreOld;
      _usedVars = new HashSet<Variable>();
      _oldVarsUsed = new HashSet<Variable>();
      insideOldExpr = 0;
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      if (!_ignoreOld)
      {
        insideOldExpr++;
        node.Expr = this.VisitExpr(node.Expr);
        insideOldExpr--;
      }
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (node.Decl != null)
      {
        _usedVars.Add(node.Decl);
        if (insideOldExpr > 0)
        {
          _oldVarsUsed.Add(node.Decl);
        }
      }
      return node;
    }

    public static IEnumerable<Variable> Collect(Absy node, bool ignoreOld = false)
    {
      var collector = new VariableCollector(ignoreOld);
      collector.Visit(node);
      return collector.usedVars;
    }

    public static IEnumerable<Variable> Collect(IEnumerable<Absy> nodes, bool ignoreOld = false)
    {
      var collector = new VariableCollector(ignoreOld);
      foreach (var node in nodes)
      {
        collector.Visit(node);
      }
      return collector.usedVars;
    }
  }

  public class BlockCoalescer : ReadOnlyVisitor
  {
    public static void CoalesceBlocks(Program program)
    {
      Contract.Requires(program != null);
      BlockCoalescer blockCoalescer = new BlockCoalescer();
      blockCoalescer.Visit(program);
    }

    private static HashSet<Block /*!*/> /*!*/ ComputeMultiPredecessorBlocks(Implementation /*!*/ impl)
    {
      Contract.Requires(impl != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Block>>()));
      HashSet<Block /*!*/> visitedBlocks = new HashSet<Block /*!*/>();
      HashSet<Block /*!*/> multiPredBlocks = new HashSet<Block /*!*/>();
      Stack<Block /*!*/> dfsStack = new Stack<Block /*!*/>();
      dfsStack.Push(impl.Blocks[0]);
      while (dfsStack.Count > 0)
      {
        Block /*!*/
          b = dfsStack.Pop();
        Contract.Assert(b != null);
        if (visitedBlocks.Contains(b))
        {
          multiPredBlocks.Add(b);
          continue;
        }

        visitedBlocks.Add(b);
        if (b.TransferCmd == null)
        {
          continue;
        }

        if (b.TransferCmd is ReturnCmd)
        {
          continue;
        }

        Contract.Assert(b.TransferCmd is GotoCmd);
        GotoCmd gotoCmd = (GotoCmd) b.TransferCmd;
        if (gotoCmd.labelTargets == null)
        {
          continue;
        }

        foreach (Block /*!*/ succ in gotoCmd.labelTargets)
        {
          Contract.Assert(succ != null);
          dfsStack.Push(succ);
        }
      }

      return multiPredBlocks;
    }

    public override Implementation VisitImplementation(Implementation impl)
    {
      //Contract.Requires(impl != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      //Console.WriteLine("Procedure {0}", impl.Name);
      //Console.WriteLine("Initial number of blocks = {0}", impl.Blocks.Count);

      HashSet<Block /*!*/> multiPredBlocks = ComputeMultiPredecessorBlocks(impl);
      Contract.Assert(Cce.NonNullElements(multiPredBlocks));
      HashSet<Block /*!*/> visitedBlocks = new HashSet<Block /*!*/>();
      HashSet<Block /*!*/> removedBlocks = new HashSet<Block /*!*/>();
      Stack<Block /*!*/> dfsStack = new Stack<Block /*!*/>();
      dfsStack.Push(impl.Blocks[0]);
      while (dfsStack.Count > 0)
      {
        Block /*!*/
          b = dfsStack.Pop();
        Contract.Assert(b != null);
        if (visitedBlocks.Contains(b))
        {
          continue;
        }

        visitedBlocks.Add(b);
        if (b.TransferCmd == null)
        {
          continue;
        }

        if (b.TransferCmd is ReturnCmd)
        {
          continue;
        }

        Contract.Assert(b.TransferCmd is GotoCmd);
        GotoCmd gotoCmd = (GotoCmd) b.TransferCmd;
        if (gotoCmd.labelTargets == null)
        {
          continue;
        }

        if (gotoCmd.labelTargets.Count == 1)
        {
          Block /*!*/
            succ = Cce.NonNull(gotoCmd.labelTargets[0]);
          if (!multiPredBlocks.Contains(succ))
          {
            foreach (Cmd /*!*/ cmd in succ.Cmds)
            {
              Contract.Assert(cmd != null);
              b.Cmds.Add(cmd);
            }

            b.TransferCmd = succ.TransferCmd;
            if (!b.tok.IsValid && succ.tok.IsValid)
            {
              b.tok = succ.tok;
              b.Label = succ.Label;
            }

            removedBlocks.Add(succ);
            dfsStack.Push(b);
            visitedBlocks.Remove(b);
            continue;
          }
        }

        foreach (Block /*!*/ succ in gotoCmd.labelTargets)
        {
          Contract.Assert(succ != null);
          dfsStack.Push(succ);
        }
      }

      List<Block /*!*/> newBlocks = new List<Block /*!*/>();
      foreach (Block /*!*/ b in impl.Blocks)
      {
        Contract.Assert(b != null);
        if (visitedBlocks.Contains(b) && !removedBlocks.Contains(b))
        {
          newBlocks.Add(b);
        }
      }

      impl.Blocks = newBlocks;
      foreach (Block b in impl.Blocks)
      {
        if (b.TransferCmd is ReturnCmd)
        {
          continue;
        }

        GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
        gotoCmd.labelNames = new List<string>();
        foreach (Block succ in gotoCmd.labelTargets)
        {
          gotoCmd.labelNames.Add(succ.Label);
        }
      }

      // Console.WriteLine("Final number of blocks = {0}", impl.Blocks.Count);
      return impl;
    }
  }

  public class LiveVariableAnalysis
  {
    private CoreOptions options;

    public LiveVariableAnalysis(CoreOptions options)
    {
      this.options = options;
    }

    public static void ClearLiveVariables(Implementation impl)
    {
      Contract.Requires(impl != null);
      foreach (Block /*!*/ block in impl.Blocks)
      {
        Contract.Assert(block != null);
        block.liveVarsBefore = null;
      }
    }

    public void ComputeLiveVariables(Implementation impl)
    {
      Contract.Requires(impl != null);
      Microsoft.Boogie.Helpers.ExtraTraceInformation(options, "Starting live variable analysis");
      Graph<Block> dag = Program.GraphFromBlocks(impl.Blocks, false);
      IEnumerable<Block> sortedNodes;
      if (options.ModifyTopologicalSorting)
      {
        sortedNodes = dag.TopologicalSort(true);
      }
      else
      {
        sortedNodes = dag.TopologicalSort();
      }

      foreach (Block /*!*/ block in sortedNodes)
      {
        Contract.Assert(block != null);
        HashSet<Variable /*!*/> /*!*/
          liveVarsAfter = new HashSet<Variable /*!*/>();

        // The injected assumption variables should always be considered to be live.
        foreach (var v in impl.InjectedAssumptionVariables.Concat(impl.DoomedInjectedAssumptionVariables))
        {
          liveVarsAfter.Add(v);
        }

        if (block.TransferCmd is GotoCmd)
        {
          GotoCmd gotoCmd = (GotoCmd) block.TransferCmd;
          if (gotoCmd.labelTargets != null)
          {
            foreach (Block /*!*/ succ in gotoCmd.labelTargets)
            {
              Contract.Assert(succ != null);
              Contract.Assert(succ.liveVarsBefore != null);
              liveVarsAfter.UnionWith(succ.liveVarsBefore);
            }
          }
        }

        List<Cmd> cmds = block.Cmds;
        int len = cmds.Count;
        for (int i = len - 1; i >= 0; i--)
        {
          if (cmds[i] is CallCmd)
          {
            Procedure /*!*/
              proc = Cce.NonNull(Cce.NonNull((CallCmd /*!*/) cmds[i]).Proc);
            if (InterProcGenKill.HasSummary(proc.Name))
            {
              liveVarsAfter =
                InterProcGenKill.PropagateLiveVarsAcrossCall(options, Cce.NonNull((CallCmd /*!*/) cmds[i]), liveVarsAfter);
              continue;
            }
          }

          Propagate(cmds[i], liveVarsAfter);
        }

        block.liveVarsBefore = liveVarsAfter;
      }
    }

    // perform in place update of liveSet
    public void Propagate(Cmd cmd, HashSet<Variable /*!*/> /*!*/ liveSet)
    {
      Contract.Requires(cmd != null);
      Contract.Requires(Cce.NonNullElements(liveSet));
      if (cmd is AssignCmd)
      {
        AssignCmd /*!*/
          assignCmd = (AssignCmd) Cce.NonNull(cmd);
        // I must first iterate over all the targets and remove the live ones.
        // After the removals are done, I must add the variables referred on 
        // the right side of the removed targets

        AssignCmd simpleAssignCmd = assignCmd.AsSimpleAssignCmd;
        HashSet<int> indexSet = new HashSet<int>();
        int index = 0;
        foreach (AssignLhs /*!*/ lhs in simpleAssignCmd.Lhss)
        {
          Contract.Assert(lhs != null);
          SimpleAssignLhs salhs = lhs as SimpleAssignLhs;
          Contract.Assert(salhs != null);
          Variable var = salhs.DeepAssignedVariable;
          if (var != null && liveSet.Contains(var))
          {
            indexSet.Add(index);
            liveSet.Remove(var);
          }

          index++;
        }

        index = 0;
        foreach (Expr /*!*/ expr in simpleAssignCmd.Rhss)
        {
          Contract.Assert(expr != null);
          if (indexSet.Contains(index))
          {
            VariableCollector /*!*/
              collector = new VariableCollector();
            collector.Visit(expr);
            liveSet.UnionWith(collector.usedVars);
          }

          index++;
        }
      }
      else if (cmd is HavocCmd)
      {
        HavocCmd /*!*/
          havocCmd = (HavocCmd) cmd;
        foreach (IdentifierExpr /*!*/ expr in havocCmd.Vars)
        {
          Contract.Assert(expr != null);
          if (expr.Decl != null && !(QKeyValue.FindBoolAttribute(expr.Decl.Attributes, "assumption") &&
                                     expr.Decl.Name.StartsWith("a##cached##")))
          {
            liveSet.Remove(expr.Decl);
          }
        }
      }
      else if (cmd is PredicateCmd)
      {
        Contract.Assert((cmd is AssertCmd || cmd is AssumeCmd));
        PredicateCmd /*!*/
          predicateCmd = (PredicateCmd) Cce.NonNull(cmd);
        if (predicateCmd.Expr is LiteralExpr)
        {
          LiteralExpr le = (LiteralExpr) predicateCmd.Expr;
          if (le.IsFalse)
          {
            liveSet.Clear();
          }
        }
        else
        {
          VariableCollector /*!*/
            collector = new VariableCollector();
          collector.Visit(predicateCmd.Expr);
          liveSet.UnionWith(collector.usedVars);
        }
      }
      else if (cmd is CommentCmd)
      {
        // comments are just for debugging and don't affect verification
      } else if (cmd is HideRevealCmd)
      {
        // reveal references no variables
      } else if (cmd is ChangeScope)
      {
      }
      else if (cmd is SugaredCmd)
      {
        SugaredCmd /*!*/
          sugCmd = (SugaredCmd) Cce.NonNull(cmd);
        Propagate(sugCmd.GetDesugaring(options), liveSet);
      }
      else if (cmd is StateCmd)
      {
        StateCmd /*!*/
          stCmd = (StateCmd) Cce.NonNull(cmd);
        List<Cmd> /*!*/
          cmds = Cce.NonNull(stCmd.Cmds);
        int len = cmds.Count;
        for (int i = len - 1; i >= 0; i--)
        {
          Propagate(cmds[i], liveSet);
        }

        foreach (Variable /*!*/ v in stCmd.Locals)
        {
          Contract.Assert(v != null);
          liveSet.Remove(v);
        }
      }
      else
      {
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        }
      }
    }
  }

  /*
  // An idempotent semiring interface
  abstract public class Weight {
     abstract public Weight! one();
     abstract public Weight! zero();
     abstract public Weight! extend(Weight! w1, Weight! w2);
     abstract public Weight! combine(Weight! w1, Weight! w2);
     abstract public Weight! isEqual(Weight! w);
     abstract public Weight! projectLocals()
  }
  */

  // Weight domain for LiveVariableAnalysis (Gen/Kill)

  public class GenKillWeight
  {
    // lambda S. (S - kill) union gen
    HashSet<Variable /*!*/> /*!*/
      gen;

    HashSet<Variable /*!*/> /*!*/
      kill;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(gen));
      Contract.Invariant(Cce.NonNullElements(kill));
      Contract.Invariant(oneWeight != null);
      Contract.Invariant(zeroWeight != null);
    }

    bool isZero;

    public static GenKillWeight /*!*/
      oneWeight = new GenKillWeight(new HashSet<Variable /*!*/>(), new HashSet<Variable /*!*/>());

    public static GenKillWeight /*!*/
      zeroWeight = new GenKillWeight();

    // initializes to zero
    public GenKillWeight()
    {
      this.isZero = true;
      this.gen = new HashSet<Variable /*!*/>();
      this.kill = new HashSet<Variable /*!*/>();
    }

    public GenKillWeight(HashSet<Variable /*!*/> gen, HashSet<Variable /*!*/> kill)
    {
      Contract.Requires(Cce.NonNullElements(gen));
      Contract.Requires(Cce.NonNullElements(kill));
      Contract.Assert(gen != null);
      Contract.Assert(kill != null);
      this.gen = gen;
      this.kill = kill;
      this.isZero = false;
    }

    public static GenKillWeight one()
    {
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      return oneWeight;
    }

    public static GenKillWeight zero()
    {
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      return zeroWeight;
    }

    public static GenKillWeight extend(GenKillWeight w1, GenKillWeight w2)
    {
      Contract.Requires(w2 != null);
      Contract.Requires(w1 != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      if (w1.isZero || w2.isZero)
      {
        return zero();
      }

      HashSet<Variable> t = new HashSet<Variable>(w2.gen);
      t.ExceptWith(w1.kill);
      HashSet<Variable> g = new HashSet<Variable>(w1.gen);
      g.UnionWith(t);
      HashSet<Variable> k = new HashSet<Variable>(w1.kill);
      k.UnionWith(w2.kill);
      return new GenKillWeight(g, k);
      //return new GenKillWeight(w1.gen.Union(w2.gen.Difference(w1.kill)), w1.kill.Union(w2.kill));
    }

    public static GenKillWeight combine(GenKillWeight w1, GenKillWeight w2)
    {
      Contract.Requires(w2 != null);
      Contract.Requires(w1 != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      if (w1.isZero)
      {
        return w2;
      }

      if (w2.isZero)
      {
        return w1;
      }

      HashSet<Variable> g = new HashSet<Variable>(w1.gen);
      g.UnionWith(w2.gen);
      HashSet<Variable> k = new HashSet<Variable>(w1.kill);
      k.IntersectWith(w2.kill);
      return new GenKillWeight(g, k);
      //return new GenKillWeight(w1.gen.Union(w2.gen), w1.kill.Intersection(w2.kill));
    }

    public static GenKillWeight projectLocals(GenKillWeight w)
    {
      Contract.Requires(w != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      HashSet<Variable /*!*/> gen = new HashSet<Variable>();
      foreach (Variable v in w.gen)
      {
        if (isGlobal(v))
        {
          gen.Add(v);
        }
      }

      HashSet<Variable /*!*/> kill = new HashSet<Variable>();
      foreach (Variable v in w.kill)
      {
        if (isGlobal(v))
        {
          kill.Add(v);
        }
      }

      return new GenKillWeight(gen, kill);
    }

    public static bool isEqual(GenKillWeight w1, GenKillWeight w2)
    {
      Contract.Requires(w2 != null);
      Contract.Requires(w1 != null);
      if (w1.isZero)
      {
        return w2.isZero;
      }

      if (w2.isZero)
      {
        return w1.isZero;
      }

      return (w1.gen.Equals(w2.gen) && w1.kill.Equals(w2.kill));
    }

    private static bool isGlobal(Variable v)
    {
      Contract.Requires(v != null);
      return (v is GlobalVariable);
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return string.Format("({0},{1})", gen.ToString(), kill.ToString());
    }

    public HashSet<Variable /*!*/> /*!*/ getLiveVars()
    {
      Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      return gen;
    }

    public HashSet<Variable /*!*/> /*!*/ getLiveVars(HashSet<Variable /*!*/> /*!*/ lv)
    {
      Contract.Requires(Cce.NonNullElements(lv));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      HashSet<Variable> temp = new HashSet<Variable>(lv);
      temp.ExceptWith(kill);
      temp.UnionWith(gen);
      return temp;
    }
  }

  public class ImplementationControlFlowGraph
  {
    public Graph<Block /*!*/> /*!*/
      graph;

    // Map from procedure to the list of blocks that call that procedure
    public Dictionary<string /*!*/, List<Block /*!*/> /*!*/> /*!*/
      procsCalled;

    public HashSet<Block /*!*/> /*!*/
      nodes;

    public Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/> /*!*/
      succEdges;

    public Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/> /*!*/
      predEdges;

    private Dictionary<Block /*!*/, int> /*!*/
      priority;

    public HashSet<Block /*!*/> /*!*/
      srcNodes;

    public HashSet<Block /*!*/> /*!*/
      exitNodes;

    public Dictionary<Block /*!*/, GenKillWeight /*!*/> /*!*/
      weightBefore;

    public Dictionary<Block /*!*/, GenKillWeight /*!*/> /*!*/
      weightAfter;

    public Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
      liveVarsAfter;

    public Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
      liveVarsBefore;

    public GenKillWeight /*!*/
      summary;

    private readonly CoreOptions options;

    public Implementation /*!*/
      impl;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(graph.Nodes));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(procsCalled));
      Contract.Invariant(Cce.NonNullElements(nodes));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(succEdges));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(predEdges));
      Contract.Invariant(priority != null);
      Contract.Invariant(Cce.NonNullElements(srcNodes));
      Contract.Invariant(Cce.NonNullElements(exitNodes));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(weightBefore));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(weightAfter));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(liveVarsAfter));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(liveVarsBefore));
      Contract.Invariant(summary != null);
      Contract.Invariant(impl != null);
    }


    [NotDelayed]
    public ImplementationControlFlowGraph(CoreOptions options, Implementation impl)
    {
      Contract.Requires(impl != null);
      this.graph = new Graph<Block /*!*/>();
      this.procsCalled = new Dictionary<string /*!*/, List<Block /*!*/> /*!*/>();
      this.nodes = new HashSet<Block /*!*/>();
      this.succEdges = new Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/>();
      this.predEdges = new Dictionary<Block /*!*/, HashSet<Block /*!*/> /*!*/>();

      this.priority = new Dictionary<Block /*!*/, int>();

      this.srcNodes = new HashSet<Block /*!*/>();
      this.exitNodes = new HashSet<Block /*!*/>();

      this.weightBefore = new Dictionary<Block /*!*/, GenKillWeight /*!*/>();
      this.weightAfter = new Dictionary<Block /*!*/, GenKillWeight /*!*/>();
      this.liveVarsAfter = new Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/>();
      this.liveVarsBefore = new Dictionary<Block /*!*/, HashSet<Variable /*!*/> /*!*/>();

      summary = GenKillWeight.zero();
      this.options = options;
      this.impl = impl;

      Initialize(impl);
    }

    private void Initialize(Implementation impl)
    {
      Contract.Requires(impl != null);
      addSource(impl.Blocks[0]);
      graph.AddSource(impl.Blocks[0]);

      foreach (Block /*!*/ b in impl.Blocks)
      {
        Contract.Assert(b != null);
        if (b.TransferCmd is ReturnCmd)
        {
          exitNodes.Add(b);
        }
        else
        {
          GotoCmd gc = b.TransferCmd as GotoCmd;
          Contract.Assert(gc != null);
          Contract.Assert(gc.labelTargets != null);
          foreach (Block /*!*/ t in gc.labelTargets)
          {
            Contract.Assert(t != null);
            addEdge(b, t);
            graph.AddEdge(b, t);
          }
        }

        weightBefore[b] = GenKillWeight.zero();
        weightAfter[b] = GenKillWeight.zero();

        foreach (Cmd /*!*/ c in b.Cmds)
        {
          Contract.Assert(c != null);
          if (c is CallCmd)
          {
            CallCmd /*!*/
              cc = Cce.NonNull((CallCmd /*!*/) c);
            Contract.Assert(cc.Proc != null);
            string /*!*/
              procName = cc.Proc.Name;
            Contract.Assert(procName != null);
            if (!procsCalled.ContainsKey(procName))
            {
              procsCalled.Add(procName, new List<Block /*!*/>());
            }

            procsCalled[procName].Add(b);
          }
        }
      }

      graph.TarjanTopSort(out var acyclic, out var sortedNodes);

      if (!acyclic)
      {
        options.OutputWriter.WriteLine("Warning: graph is not a dag");
      }

      int num = sortedNodes.Count;
      foreach (Block /*!*/ b in sortedNodes)
      {
        Contract.Assert(b != null);
        priority.Add(b, num);
        num--;
      }
    }

    public int getPriority(Block b)
    {
      Contract.Requires(b != null);
      if (priority.ContainsKey(b))
      {
        return priority[b];
      }

      return Int32.MaxValue;
    }

    private void addSource(Block b)
    {
      Contract.Requires(b != null);
      registerNode(b);
      this.srcNodes.Add(b);
    }

    private void addExit(Block b)
    {
      Contract.Requires(b != null);
      registerNode(b);
      this.exitNodes.Add(b);
    }

    private void registerNode(Block b)
    {
      Contract.Requires(b != null);
      if (!succEdges.ContainsKey(b))
      {
        succEdges.Add(b, new HashSet<Block /*!*/>());
      }

      if (!predEdges.ContainsKey(b))
      {
        predEdges.Add(b, new HashSet<Block /*!*/>());
      }

      nodes.Add(b);
    }

    private void addEdge(Block src, Block tgt)
    {
      Contract.Requires(tgt != null);
      Contract.Requires(src != null);
      registerNode(src);
      registerNode(tgt);

      succEdges[src].Add(tgt);
      predEdges[tgt].Add(src);
    }
  }

  // Interprocedural Gen/Kill Analysis
  public class InterProcGenKill
  {
    private CoreOptions options;
    Program /*!*/ program;

    Dictionary<string /*!*/, ImplementationControlFlowGraph /*!*/> /*!*/
      procICFG;

    Dictionary<string /*!*/, Procedure /*!*/> /*!*/
      name2Proc;

    Dictionary<string /*!*/, List<WorkItem /*!*/> /*!*/> /*!*/
      callers;

    Graph<string /*!*/> /*!*/
      callGraph;

    Dictionary<string /*!*/, int> /*!*/
      procPriority;

    int maxBlocksInProc;

    WorkList /*!*/
      workList;

    Implementation /*!*/
      mainImpl;

    static Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
      varsLiveAtExit = new Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/>();

    static Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
      varsLiveAtEntry = new Dictionary<string /*!*/, HashSet<Variable /*!*/> /*!*/>();

    static Dictionary<string /*!*/, GenKillWeight /*!*/> /*!*/
      varsLiveSummary = new Dictionary<string /*!*/, GenKillWeight /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(workList != null);
      Contract.Invariant(mainImpl != null);
      Contract.Invariant(program != null);
      Contract.Invariant(Cce.NonNullDictionaryAndValues(procICFG));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(name2Proc));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(callers) &&
                         Contract.ForAll(callers.Values, v => Cce.NonNullElements(v)));
      Contract.Invariant(Cce.NonNullElements(callGraph.Nodes));
      Contract.Invariant(procPriority != null);
      Contract.Invariant(Cce.NonNullDictionaryAndValues(varsLiveAtEntry));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(varsLiveAtExit) &&
                         Contract.ForAll(varsLiveAtExit.Values, v => Cce.NonNullElements(v)));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(varsLiveSummary));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(weightCacheAfterCall));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(weightCacheBeforeCall));
    }


    [NotDelayed]
    public InterProcGenKill(Implementation impl, Program program, CoreOptions options)
    {
      Contract.Requires(program != null);
      Contract.Requires(impl != null);
      this.program = program;
      this.options = options;
      procICFG = new Dictionary<string /*!*/, ImplementationControlFlowGraph /*!*/>();
      name2Proc = new Dictionary<string /*!*/, Procedure /*!*/>();
      workList = new WorkList();
      this.callers = new Dictionary<string /*!*/, List<WorkItem /*!*/> /*!*/>();
      this.callGraph = new Graph<string /*!*/>();
      this.procPriority = new Dictionary<string /*!*/, int>();
      this.maxBlocksInProc = 0;
      this.mainImpl = impl;

      Dictionary<string /*!*/, Implementation /*!*/> /*!*/
        name2Impl = new Dictionary<string /*!*/, Implementation /*!*/>();
      varsLiveAtExit.Clear();
      varsLiveAtEntry.Clear();
      varsLiveSummary.Clear();

      foreach (var decl in program.TopLevelDeclarations)
      {
        Contract.Assert(decl != null);
        if (decl is Implementation)
        {
          Implementation /*!*/
            imp = (Implementation /*!*/) Cce.NonNull(decl);
          name2Impl[imp.Name] = imp;
        }
        else if (decl is Procedure)
        {
          Procedure /*!*/
            proc = Cce.NonNull(decl as Procedure);
          name2Proc[proc.Name] = proc;
        }
      }

      ImplementationControlFlowGraph /*!*/
        mainImplementationControlFlowGraph = new ImplementationControlFlowGraph(this.options, mainImpl);
      Contract.Assert(mainImplementationControlFlowGraph != null);
      procICFG.Add(mainImplementationControlFlowGraph.impl.Name, mainImplementationControlFlowGraph);
      callGraph.AddSource(mainImplementationControlFlowGraph.impl.Name);

      List<ImplementationControlFlowGraph /*!*/> /*!*/
        procsToConsider = new List<ImplementationControlFlowGraph /*!*/>();
      procsToConsider.Add(mainImplementationControlFlowGraph);

      while (procsToConsider.Count != 0)
      {
        ImplementationControlFlowGraph /*!*/
          p = procsToConsider[0];
        Contract.Assert(p != null);
        procsToConsider.RemoveAt(0);

        foreach (string /*!*/ callee in p.procsCalled.Keys)
        {
          Contract.Assert(callee != null);
          if (!name2Impl.ContainsKey(callee))
          {
            continue;
          }

          callGraph.AddEdge(p.impl.Name, callee);

          if (maxBlocksInProc < p.nodes.Count)
          {
            maxBlocksInProc = p.nodes.Count;
          }

          if (!callers.ContainsKey(callee))
          {
            callers.Add(callee, new List<WorkItem /*!*/>());
          }

          foreach (Block /*!*/ b in p.procsCalled[callee])
          {
            Contract.Assert(b != null);
            callers[callee].Add(new WorkItem(p, b));
          }

          if (procICFG.ContainsKey(callee))
          {
            continue;
          }

          ImplementationControlFlowGraph /*!*/
            ncfg = new ImplementationControlFlowGraph(this.options, name2Impl[callee]);
          Contract.Assert(ncfg != null);
          procICFG.Add(callee, ncfg);
          procsToConsider.Add(ncfg);
        }
      }

      callGraph.TarjanTopSort(out var acyclic, out var sortedNodes);

      Contract.Assert(acyclic);

      int cnt = 0;
      for (int i = sortedNodes.Count - 1; i >= 0; i--)
      {
        string s = sortedNodes[i];
        if (s == null)
        {
          continue;
        }

        procPriority.Add(s, cnt);
        cnt++;
      }
    }

    public static HashSet<Variable /*!*/> /*!*/ GetVarsLiveAtExit(Implementation impl, Program prog)
    {
      Contract.Requires(prog != null);
      Contract.Requires(impl != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      if (varsLiveAtExit.ContainsKey(impl.Name))
      {
        return varsLiveAtExit[impl.Name];
      }

      // Return default: all globals and out params
      HashSet<Variable /*!*/> /*!*/
        lv = new HashSet<Variable /*!*/>();
      foreach (Variable /*!*/ v in prog.GlobalVariables)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      foreach (Variable /*!*/ v in impl.OutParams)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      return lv;
    }

    public static HashSet<Variable /*!*/> /*!*/ GetVarsLiveAtEntry(Implementation impl, Program prog)
    {
      Contract.Requires(prog != null);
      Contract.Requires(impl != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      if (varsLiveAtEntry.ContainsKey(impl.Name))
      {
        return varsLiveAtEntry[impl.Name];
      }

      // Return default: all globals and in params
      HashSet<Variable /*!*/> /*!*/
        lv = new HashSet<Variable /*!*/>();
      foreach (Variable /*!*/ v in prog.GlobalVariables)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      foreach (Variable /*!*/ v in impl.InParams)
      {
        Contract.Assert(v != null);
        lv.Add(v);
      }

      return lv;
    }

    public static bool HasSummary(string name)
    {
      Contract.Requires(name != null);
      return varsLiveSummary.ContainsKey(name);
    }

    public static HashSet<Variable /*!*/> /*!*/
      PropagateLiveVarsAcrossCall(CoreOptions options, CallCmd cmd, HashSet<Variable /*!*/> /*!*/ lvAfter)
    {
      Contract.Requires(cmd != null);
      Contract.Requires(Cce.NonNullElements(lvAfter));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
      Procedure /*!*/
        proc = Cce.NonNull(cmd.Proc);
      if (varsLiveSummary.ContainsKey(proc.Name))
      {
        GenKillWeight /*!*/
          w1 = getWeightBeforeCall(cmd);
        Contract.Assert(w1 != null);
        GenKillWeight /*!*/
          w2 = varsLiveSummary[proc.Name];
        Contract.Assert(w2 != null);
        GenKillWeight /*!*/
          w3 = getWeightAfterCall(cmd);
        Contract.Assert(w3 != null);
        GenKillWeight /*!*/
          w = GenKillWeight.extend(w1, GenKillWeight.extend(w2, w3));
        Contract.Assert(w != null);
        return w.getLiveVars(lvAfter);
      }

      HashSet<Variable /*!*/> /*!*/
        ret = new HashSet<Variable /*!*/>();
      ret.UnionWith(lvAfter);
      new LiveVariableAnalysis(options).Propagate(cmd, ret);
      return ret;
    }

    class WorkItem
    {
      public ImplementationControlFlowGraph /*!*/
        cfg;

      public Block /*!*/
        block;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(cfg != null);
        Contract.Invariant(block != null);
      }


      public WorkItem(ImplementationControlFlowGraph cfg, Block block)
      {
        Contract.Requires(block != null);
        Contract.Requires(cfg != null);
        this.cfg = cfg;
        this.block = block;
      }

      public GenKillWeight getWeightAfter()
      {
        Contract.Ensures(Contract.Result<GenKillWeight>() != null);
        return cfg.weightAfter[block];
      }

      public bool setWeightBefore(GenKillWeight w)
      {
        Contract.Requires(w != null);
        GenKillWeight /*!*/
          prev = cfg.weightBefore[block];
        Contract.Assert(prev != null);
        GenKillWeight /*!*/
          curr = GenKillWeight.combine(w, prev);
        Contract.Assert(curr != null);
        if (GenKillWeight.isEqual(prev, curr))
        {
          return false;
        }

        cfg.weightBefore[block] = curr;
        return true;
      }

      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object other)
      {
        WorkItem /*!*/
          wi = (WorkItem /*!*/) Cce.NonNull(other);
        return (wi.cfg == cfg && wi.block == block);
      }

      [Pure]
      public override int GetHashCode()
      {
        return 0;
      }

      public string getLabel()
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return cfg.impl.Name + "::" + block.Label;
      }
    }

    private void AddToWorkList(WorkItem wi)
    {
      Contract.Requires(wi != null);
      int i = procPriority[wi.cfg.impl.Name];
      int j = wi.cfg.getPriority(wi.block);
      int priority = (i * maxBlocksInProc) + j;

      workList.Add(wi, priority);
    }

    private void AddToWorkListReverse(WorkItem wi)
    {
      Contract.Requires(wi != null);
      int i = procPriority[wi.cfg.impl.Name];
      int j = wi.cfg.getPriority(wi.block);
      int priority = (procPriority.Count - i) * maxBlocksInProc + j;
      workList.Add(wi, priority);
    }

    class WorkList
    {
      SortedList<int, int> /*!*/
        priorities;

      HashSet<string /*!*/> /*!*/
        labels;

      Dictionary<int, List<WorkItem /*!*/> /*!*/> /*!*/
        workList;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(priorities != null);
        Contract.Invariant(Cce.NonNullElements(labels));
        Contract.Invariant(Cce.NonNullDictionaryAndValues(workList) &&
                           Contract.ForAll(workList.Values, v => Cce.NonNullElements(v)));
      }


      public WorkList()
      {
        labels = new HashSet<string /*!*/>();
        priorities = new SortedList<int, int>();
        workList = new Dictionary<int, List<WorkItem /*!*/> /*!*/>();
      }

      public void Add(WorkItem wi, int priority)
      {
        Contract.Requires(wi != null);
        string /*!*/
          lab = wi.getLabel();
        Contract.Assert(lab != null);
        if (labels.Contains(lab))
        {
          // Already on worklist
          return;
        }

        labels.Add(lab);
        if (!workList.ContainsKey(priority))
        {
          workList.Add(priority, new List<WorkItem /*!*/>());
        }

        workList[priority].Add(wi);
        if (!priorities.ContainsKey(priority))
        {
          priorities.Add(priority, 0);
        }

        priorities[priority] = priorities[priority] + 1;
      }

      public WorkItem Get()
      {
        Contract.Ensures(Contract.Result<WorkItem>() != null);
        // Get minimum priority
        int p = Cce.NonNull(priorities.Keys)[0];
        priorities[p] = priorities[p] - 1;
        if (priorities[p] == 0)
        {
          priorities.Remove(p);
        }

        // Get a WI with this priority
        WorkItem /*!*/
          wi = workList[p][0];
        Contract.Assert(wi != null);
        workList[p].RemoveAt(0);

        // update labels
        labels.Remove(wi.getLabel());
        return wi;
      }

      public int Count
      {
        get { return labels.Count; }
      }
    }

    private GenKillWeight getSummary(CallCmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      Contract.Assert(cmd.Proc != null);
      string /*!*/
        procName = cmd.Proc.Name;
      Contract.Assert(procName != null);
      if (procICFG.ContainsKey(procName))
      {
        ImplementationControlFlowGraph /*!*/
          cfg = procICFG[procName];
        Contract.Assert(cfg != null);
        return GenKillWeight.projectLocals(cfg.summary);
      }

      {
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      }
    }

    public void ComputeLiveVars(Implementation impl, Program /*!*/ prog)
    {
      Contract.Requires(prog != null);
      Contract.Requires(impl != null);
      InterProcGenKill /*!*/
        ipgk = new InterProcGenKill(impl, prog, options);
      Contract.Assert(ipgk != null);
      ipgk.Compute();
    }

    public void Compute()
    {
      // Put all exit nodes in the worklist
      foreach (ImplementationControlFlowGraph /*!*/ cfg in procICFG.Values)
      {
        Contract.Assert(cfg != null);
        foreach (Block /*!*/ eb in cfg.exitNodes)
        {
          Contract.Assert(eb != null);
          WorkItem /*!*/
            wi = new WorkItem(cfg, eb);
          Contract.Assert(wi != null);
          cfg.weightAfter[eb] = GenKillWeight.one();
          AddToWorkList(wi);
        }
      }

      while (workList.Count != 0)
      {
        WorkItem /*!*/
          wi = workList.Get();
        Contract.Assert(wi != null);
        process(wi);
      }

      // Propagate LV to all procedures
      foreach (ImplementationControlFlowGraph /*!*/ cfg in procICFG.Values)
      {
        Contract.Assert(cfg != null);
        foreach (Block /*!*/ b in cfg.nodes)
        {
          Contract.Assert(b != null);
          cfg.liveVarsAfter.Add(b, new HashSet<Variable /*!*/>());
          cfg.liveVarsBefore.Add(b, new HashSet<Variable /*!*/>());
        }
      }

      ImplementationControlFlowGraph /*!*/
        mainCfg = procICFG[mainImpl.Name];
      Contract.Assert(mainCfg != null);
      foreach (Block /*!*/ eb in mainCfg.exitNodes)
      {
        Contract.Assert(eb != null);
        WorkItem /*!*/
          wi = new WorkItem(mainCfg, eb);
        Contract.Assert(wi != null);
        AddToWorkListReverse(wi);
      }

      while (workList.Count != 0)
      {
        WorkItem /*!*/
          wi = workList.Get();
        Contract.Assert(wi != null);
        ProcessLv(wi);
      }

      // Set live variable info
      foreach (ImplementationControlFlowGraph /*!*/ cfg in procICFG.Values)
      {
        Contract.Assert(cfg != null);
        HashSet<Variable /*!*/> /*!*/
          lv = new HashSet<Variable /*!*/>();
        foreach (Block /*!*/ eb in cfg.exitNodes)
        {
          Contract.Assert(eb != null);
          lv.UnionWith(cfg.liveVarsAfter[eb]);
        }

        varsLiveAtExit.Add(cfg.impl.Name, lv);
        lv = new HashSet<Variable /*!*/>();
        foreach (Block /*!*/ eb in cfg.srcNodes)
        {
          Contract.Assert(eb != null);
          lv.UnionWith(cfg.liveVarsBefore[eb]);
        }

        varsLiveAtEntry.Add(cfg.impl.Name, lv);
        varsLiveSummary.Add(cfg.impl.Name, cfg.summary);
      }

      /*
      foreach(Block/*!*/
      /* b in mainImpl.Blocks){
Contract.Assert(b != null);
//Set<Variable!> lv = cfg.weightBefore[b].getLiveVars();
b.liveVarsBefore = procICFG[mainImpl.Name].liveVarsAfter[b];
//foreach(GlobalVariable/*!*/
      /* v in program.GlobalVariables){Contract.Assert(v != null);
//  b.liveVarsBefore.Add(v);
//}
}
*/
    }

    // Called when summaries have already been computed
    private void ProcessLv(WorkItem wi)
    {
      Contract.Requires(wi != null);
      ImplementationControlFlowGraph /*!*/
        cfg = wi.cfg;
      Contract.Assert(cfg != null);
      Block /*!*/
        block = wi.block;
      Contract.Assert(block != null);
      HashSet<Variable /*!*/> /*!*/
        lv = cfg.liveVarsAfter[block];
      Contract.Assert(Cce.NonNullElements(lv));
      // Propagate backwards in the block
      HashSet<Variable /*!*/> /*!*/
        prop = new HashSet<Variable /*!*/>();
      prop.UnionWith(lv);
      for (int i = block.Cmds.Count - 1; i >= 0; i--)
      {
        Cmd /*!*/
          cmd = block.Cmds[i];
        Contract.Assert(cmd != null);
        if (cmd is CallCmd)
        {
          string /*!*/
            procName = Cce.NonNull(Cce.NonNull((CallCmd) cmd).Proc).Name;
          Contract.Assert(procName != null);
          if (procICFG.ContainsKey(procName))
          {
            ImplementationControlFlowGraph /*!*/
              callee = procICFG[procName];
            Contract.Assert(callee != null);
            // Inter propagation
            // Remove local variables; add return variables
            HashSet<Variable /*!*/> /*!*/
              elv = new HashSet<Variable /*!*/>();
            foreach (Variable /*!*/ v in prop)
            {
              Contract.Assert(v != null);
              if (v is GlobalVariable)
              {
                elv.Add(v);
              }
            }

            foreach (Variable /*!*/ v in callee.impl.OutParams)
            {
              Contract.Assert(v != null);
              elv.Add(v);
            }

            foreach (Block /*!*/ eb in callee.exitNodes)
            {
              Contract.Assert(eb != null);
              callee.liveVarsAfter[eb].UnionWith(elv);
              // TODO: check if modified before inserting
              AddToWorkListReverse(new WorkItem(callee, eb));
            }

            // Continue with intra propagation
            GenKillWeight /*!*/
              summary = GetWeightCall(Cce.NonNull((CallCmd /*!*/) cmd));
            prop = summary.getLiveVars(prop);
          }
          else
          {
            new LiveVariableAnalysis(options).Propagate(cmd, prop);
          }
        }
        else
        {
          new LiveVariableAnalysis(options).Propagate(cmd, prop);
        }
      }

      cfg.liveVarsBefore[block].UnionWith(prop);

      foreach (Block /*!*/ b in cfg.predEdges[block])
      {
        Contract.Assert(b != null);
        HashSet<Variable /*!*/> /*!*/
          prev = cfg.liveVarsAfter[b];
        Contract.Assert(Cce.NonNullElements(prev));
        HashSet<Variable /*!*/> /*!*/
          curr = new HashSet<Variable>(prev);
        curr.UnionWith(cfg.liveVarsBefore[block]);
        Contract.Assert(Cce.NonNullElements(curr));
        if (curr.Count != prev.Count)
        {
          cfg.liveVarsAfter[b] = curr;
          AddToWorkListReverse(new WorkItem(cfg, b));
        }
      }
    }

    private void process(WorkItem wi)
    {
      Contract.Requires(wi != null);
      GenKillWeight /*!*/
        w = wi.getWeightAfter();
      Contract.Assert(w != null);

      for (int i = wi.block.Cmds.Count - 1; i >= 0; i--)
      {
        Cmd /*!*/
          c = wi.block.Cmds[i];
        Contract.Assert(c != null);
        if (c is CallCmd && procICFG.ContainsKey(Cce.NonNull(Cce.NonNull((CallCmd) c).Proc).Name))
        {
          w = GenKillWeight.extend(GetWeightCall(Cce.NonNull((CallCmd) c)), w);
        }
        else
        {
          GenKillWeight /*!*/
            cweight = GetWeight(c, wi.cfg.impl, program);
          Contract.Assert(cweight != null);
          w = GenKillWeight.extend(cweight, w);
        }
      }

      bool change = wi.setWeightBefore(w);

      if (change && wi.cfg.srcNodes.Contains(wi.block))
      {
        GenKillWeight /*!*/
          prev = wi.cfg.summary;
        Contract.Assert(prev != null);
        GenKillWeight /*!*/
          curr = GenKillWeight.combine(prev, wi.cfg.weightBefore[wi.block]);
        Contract.Assert(curr != null);
        if (!GenKillWeight.isEqual(prev, curr))
        {
          wi.cfg.summary = curr;
          // push callers onto the worklist
          if (callers.ContainsKey(wi.cfg.impl.Name))
          {
            foreach (WorkItem /*!*/ caller in callers[wi.cfg.impl.Name])
            {
              Contract.Assert(caller != null);
              AddToWorkList(caller);
            }
          }
        }
      }

      foreach (Block /*!*/ b in wi.cfg.predEdges[wi.block])
      {
        Contract.Assert(b != null);
        GenKillWeight /*!*/
          prev = wi.cfg.weightAfter[b];
        Contract.Assert(prev != null);
        GenKillWeight /*!*/
          curr = GenKillWeight.combine(prev, w);
        Contract.Assert(curr != null);
        if (!GenKillWeight.isEqual(prev, curr))
        {
          wi.cfg.weightAfter[b] = curr;
          AddToWorkList(new WorkItem(wi.cfg, b));
        }
      }
    }

    static Dictionary<Cmd /*!*/, GenKillWeight /*!*/> /*!*/
      weightCache = new Dictionary<Cmd /*!*/, GenKillWeight /*!*/>();

    private GenKillWeight GetWeight(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      return GetWeight(cmd, null, null);
    }

    private GenKillWeight GetWeightCall(CallCmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      GenKillWeight /*!*/
        w1 = getWeightBeforeCall(cmd);
      GenKillWeight /*!*/
        w2 = getSummary(cmd);
      GenKillWeight /*!*/
        w3 = getWeightAfterCall(cmd);
      Contract.Assert(w1 != null);
      Contract.Assert(w2 != null);
      Contract.Assert(w3 != null);
      return GenKillWeight.extend(w1, GenKillWeight.extend(w2, w3));
    }

    private GenKillWeight GetWeight(Cmd cmd, Implementation impl, Program prog)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);

      if (weightCache.ContainsKey(cmd))
      {
        return weightCache[cmd];
      }

      HashSet<Variable /*!*/> /*!*/
        gen = new HashSet<Variable /*!*/>();
      HashSet<Variable /*!*/> /*!*/
        kill = new HashSet<Variable /*!*/>();
      GenKillWeight /*!*/
        ret;

      if (cmd is AssignCmd)
      {
        AssignCmd /*!*/
          assignCmd = (AssignCmd) cmd;
        Contract.Assert(cmd != null);
        // I must first iterate over all the targets and remove the live ones.
        // After the removals are done, I must add the variables referred on 
        // the right side of the removed targets
        foreach (AssignLhs /*!*/ lhs in assignCmd.Lhss)
        {
          Contract.Assert(lhs != null);
          Variable var = lhs.DeepAssignedVariable;
          if (var != null)
          {
            if (lhs is SimpleAssignLhs)
            {
              // we should only remove non-map target variables because there is an implicit
              // read of a map variable in an assignment to it
              kill.Add(var);
            }
          }
        }

        int index = 0;
        foreach (Expr /*!*/ expr in assignCmd.Rhss)
        {
          Contract.Assert(expr != null);
          VariableCollector /*!*/
            collector = new VariableCollector();
          collector.Visit(expr);
          gen.UnionWith(collector.usedVars);
          AssignLhs lhs = assignCmd.Lhss[index];
          if (lhs is MapAssignLhs)
          {
            // If the target is a map, then all indices are also read
            MapAssignLhs malhs = (MapAssignLhs) lhs;
            foreach (Expr e in malhs.Indexes)
            {
              VariableCollector /*!*/
                c = new VariableCollector();
              c.Visit(e);
              gen.UnionWith(c.usedVars);
            }
          }

          index++;
        }

        ret = new GenKillWeight(gen, kill);
      }
      else if (cmd is HavocCmd)
      {
        HavocCmd /*!*/
          havocCmd = (HavocCmd) Cce.NonNull(cmd);
        foreach (IdentifierExpr /*!*/ expr in havocCmd.Vars)
        {
          Contract.Assert(expr != null);
          if (expr.Decl != null)
          {
            kill.Add(expr.Decl);
          }
        }

        ret = new GenKillWeight(gen, kill);
      }
      else if (cmd is PredicateCmd)
      {
        Contract.Assert((cmd is AssertCmd || cmd is AssumeCmd));
        PredicateCmd /*!*/
          predicateCmd = (PredicateCmd) Cce.NonNull(cmd);
        if (predicateCmd.Expr is LiteralExpr && prog != null && impl != null)
        {
          LiteralExpr le = (LiteralExpr) predicateCmd.Expr;
          if (le.IsFalse)
          {
            var globals = prog.GlobalVariables;
            Contract.Assert(Cce.NonNullElements(globals));
            foreach (Variable /*!*/ v in globals)
            {
              Contract.Assert(v != null);
              kill.Add(v);
            }

            foreach (Variable /*!*/ v in impl.LocVars)
            {
              Contract.Assert(v != null);
              kill.Add(v);
            }

            foreach (Variable /*!*/ v in impl.OutParams)
            {
              Contract.Assert(v != null);
              kill.Add(v);
            }
          }
        }
        else
        {
          VariableCollector /*!*/
            collector = new VariableCollector();
          collector.Visit(predicateCmd.Expr);
          gen.UnionWith(collector.usedVars);
        }

        ret = new GenKillWeight(gen, kill);
      }
      else if (cmd is CommentCmd)
      {
        ret = new GenKillWeight(gen, kill);
        // comments are just for debugging and don't affect verification
      }
      else if (cmd is SugaredCmd)
      {
        SugaredCmd /*!*/
          sugCmd = (SugaredCmd) cmd;
        Contract.Assert(sugCmd != null);
        ret = GetWeight(sugCmd.GetDesugaring(options), impl, prog);
      }
      else if (cmd is StateCmd)
      {
        StateCmd /*!*/
          stCmd = (StateCmd) cmd;
        Contract.Assert(stCmd != null);
        List<Cmd> /*!*/
          cmds = stCmd.Cmds;
        Contract.Assert(cmds != null);
        int len = cmds.Count;
        ret = GenKillWeight.one();
        for (int i = len - 1; i >= 0; i--)
        {
          GenKillWeight /*!*/
            w = GetWeight(cmds[i], impl, prog);
          Contract.Assert(w != null);
          ret = GenKillWeight.extend(w, ret);
        }

        foreach (Variable /*!*/ v in stCmd.Locals)
        {
          Contract.Assert(v != null);
          kill.Add(v);
        }

        ret = GenKillWeight.extend(new GenKillWeight(gen, kill), ret);
      }
      else
      {
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        }
      }

      weightCache[cmd] = ret;
      return ret;
    }

    static Dictionary<Cmd /*!*/, GenKillWeight /*!*/> /*!*/
      weightCacheAfterCall = new Dictionary<Cmd /*!*/, GenKillWeight /*!*/>();

    static Dictionary<Cmd /*!*/, GenKillWeight /*!*/> /*!*/
      weightCacheBeforeCall = new Dictionary<Cmd /*!*/, GenKillWeight /*!*/>();

    private static GenKillWeight getWeightAfterCall(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);

      if (weightCacheAfterCall.ContainsKey(cmd))
      {
        return weightCacheAfterCall[cmd];
      }

      HashSet<Variable /*!*/> /*!*/
        gen = new HashSet<Variable /*!*/>();
      HashSet<Variable /*!*/> /*!*/
        kill = new HashSet<Variable /*!*/>();

      Contract.Assert(cmd is CallCmd);
      CallCmd /*!*/
        ccmd = Cce.NonNull((CallCmd) cmd);

      foreach (IdentifierExpr /*!*/ ie in ccmd.Outs)
      {
        Contract.Assert(ie != null);
        if (ie.Decl != null)
        {
          kill.Add(ie.Decl);
        }
      }

      // Variables in ensures are considered as "read"
      foreach (Ensures /*!*/ re in Cce.NonNull(ccmd.Proc).Ensures)
      {
        Contract.Assert(re != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(re.Condition);
        foreach (Variable /*!*/ v in collector.usedVars)
        {
          Contract.Assert(v != null);
          if (v is GlobalVariable)
          {
            gen.Add(v);
          }
        }
      }

      GenKillWeight /*!*/
        ret = new GenKillWeight(gen, kill);
      Contract.Assert(ret != null);
      weightCacheAfterCall[cmd] = ret;
      return ret;
    }

    private static GenKillWeight getWeightBeforeCall(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<GenKillWeight>() != null);
      Contract.Assert((cmd is CallCmd));
      if (weightCacheBeforeCall.ContainsKey(cmd))
      {
        return weightCacheBeforeCall[cmd];
      }

      HashSet<Variable /*!*/> /*!*/
        gen = new HashSet<Variable /*!*/>();
      HashSet<Variable /*!*/> /*!*/
        kill = new HashSet<Variable /*!*/>();
      CallCmd /*!*/
        ccmd = Cce.NonNull((CallCmd /*!*/) cmd);

      foreach (Expr /*!*/ expr in ccmd.Ins)
      {
        Contract.Assert(expr != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(expr);
        gen.UnionWith(collector.usedVars);
      }

      Contract.Assert(ccmd.Proc != null);

      // Variables in requires are considered as "read"
      foreach (Requires /*!*/ re in ccmd.Proc.Requires)
      {
        Contract.Assert(re != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(re.Condition);
        foreach (Variable /*!*/ v in collector.usedVars)
        {
          Contract.Assert(v != null);
          if (v is GlobalVariable)
          {
            gen.Add(v);
          }
        }
      }

      // Old variables in ensures are considered as "read"
      foreach (Ensures /*!*/ re in ccmd.Proc.Ensures)
      {
        Contract.Assert(re != null);
        VariableCollector /*!*/
          collector = new VariableCollector();
        collector.Visit(re.Condition);
        foreach (Variable /*!*/ v in collector.oldVarsUsed)
        {
          Contract.Assert(v != null);
          if (v is GlobalVariable)
          {
            gen.Add(v);
          }
        }
      }

      GenKillWeight /*!*/
        ret = new GenKillWeight(gen, kill);
      Contract.Assert(ret != null);
      weightCacheAfterCall[cmd] = ret;
      return ret;
    }
  }
}