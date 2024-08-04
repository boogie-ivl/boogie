using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class Action
  {
    public ActionDecl ActionDecl;
    public Action RefinedAction;
    public Implementation Impl;
    public List<AssertCmd> Gate;
    public HashSet<Variable> UsedGlobalVarsInGate;
    public HashSet<Variable> UsedGlobalVarsInAction;
    public HashSet<Variable> ModifiedGlobalVars;
    public Function InputOutputRelation;

    public List<AssertCmd> FirstGate;
    public Implementation FirstImpl;
    public List<AssertCmd> SecondGate;
    public Implementation SecondImpl;
    public Dictionary<Variable, Function> TriggerFunctions;
    
    public DatatypeTypeCtorDecl ChoiceDatatypeTypeCtorDecl;
    public Implementation ImplWithChoice;
    public Function InputOutputRelationWithChoice;

    public Action(CivlTypeChecker civlTypeChecker, ActionDecl actionDecl, Action refinedAction, bool isInvariant)
    {
      ActionDecl = actionDecl;
      RefinedAction = refinedAction;
      Impl = CreateDuplicateImplementation(actionDecl.Impl, actionDecl.Name);
      if (PendingAsyncs.Any())
      {
        DesugarCreateAsyncs(civlTypeChecker, Impl, ActionDecl);
        if (isInvariant)
        {
          ImplWithChoice = CreateDuplicateImplementation(Impl, $"{Name}_With_Choice");
          var choiceDatatypeName = $"Choice_{Name}";
          ChoiceDatatypeTypeCtorDecl =
            new DatatypeTypeCtorDecl(Token.NoToken, choiceDatatypeName, new List<TypeVariable>(), null);
          PendingAsyncs.ForEach(elim =>
          {
            var field = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, elim.Name, elim.PendingAsyncType), true);
            ChoiceDatatypeTypeCtorDecl.AddConstructor(Token.NoToken, $"{choiceDatatypeName}_{elim.Name}",
              new List<Variable>() { field });
          });
          civlTypeChecker.program.AddTopLevelDeclaration(ChoiceDatatypeTypeCtorDecl);
          DesugarSetChoice(civlTypeChecker, ImplWithChoice);
        }
        DropSetChoice(Impl);
      }

      ModifiedGlobalVars = new HashSet<Variable>(Impl.Proc.Modifies.Select(x => x.Decl));

      AddGateSufficiencyCheckerAndHoistAsserts(civlTypeChecker);

      UsedGlobalVarsInGate = new HashSet<Variable>(VariableCollector.Collect(Gate).Where(x => x is GlobalVariable));
      UsedGlobalVarsInAction = new HashSet<Variable>(VariableCollector.Collect(Impl).Where(x => x is GlobalVariable));

      InputOutputRelation = ComputeInputOutputRelation(civlTypeChecker, Impl);
      if (ImplWithChoice != null)
      {
        InputOutputRelationWithChoice = ComputeInputOutputRelation(civlTypeChecker, ImplWithChoice);
      }

      AtomicActionDuplicator.SetupCopy(this, ref FirstGate, ref FirstImpl, "first_");
      AtomicActionDuplicator.SetupCopy(this, ref SecondGate, ref SecondImpl, "second_");
      DeclareTriggerFunctions();
    }

    public IEnumerable<Variable> UsedGlobalVars => UsedGlobalVarsInGate.Union(UsedGlobalVarsInAction);

    public IToken tok => ActionDecl.tok;

    public string Name => ActionDecl.Name;

    public LayerRange LayerRange => ActionDecl.LayerRange;

    public IEnumerable<ActionDecl> PendingAsyncs => ActionDecl.CreateActionDecls;
    
    public bool HasPendingAsyncs => PendingAsyncs.Any();

    public bool IsRightMover => ActionDecl.MoverType == MoverType.Right || ActionDecl.MoverType == MoverType.Both;

    public bool IsLeftMover => ActionDecl.MoverType == MoverType.Left || ActionDecl.MoverType == MoverType.Both;

    public int PendingAsyncStartIndex => ActionDecl.OutParams.Count;

    public Expr ExitCondition => ActionDecl.FindExprAttribute("exit_condition");

    public bool TriviallyCommutesWith(Action other)
    {
      return !this.ModifiedGlobalVars.Intersect(other.UsedGlobalVarsInAction).Any() &&
             !this.UsedGlobalVarsInAction.Intersect(other.ModifiedGlobalVars).Any();
    }

    public Variable PAs(CtorType pendingAsyncType)
    {
      var pendingAsyncMultisetType = TypeHelper.MapType(pendingAsyncType, Type.Int);
      return Impl.OutParams.Skip(PendingAsyncStartIndex).First(v => v.TypedIdent.Type.Equals(pendingAsyncMultisetType));
    }

    public bool HasAssumeCmd => Impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd));

    public DatatypeConstructor ChoiceConstructor(CtorType pendingAsyncType)
    {
      return ChoiceDatatypeTypeCtorDecl.Constructors.First(x => x.InParams[0].TypedIdent.Type.Equals(pendingAsyncType));
    }

    public IEnumerable<AssertCmd> GetGateAsserts(Substitution subst, string msg)
    {
      foreach (var gate in Gate)
      {
        AssertCmd cmd = subst != null ? (AssertCmd) Substituter.Apply(subst, gate) : new AssertCmd(gate.tok, gate.Expr);
        cmd.Description = new FailureOnlyDescription(msg);
        yield return cmd;
      }
    }

    public Expr GetTransitionRelation(CivlTypeChecker civlTypeChecker, HashSet<Variable> frame)
    {
      return TransitionRelationComputation.Refinement(civlTypeChecker, Impl, frame);
    }

    public Substitution GetSubstitution(Action to)
    {
      Debug.Assert(PendingAsyncStartIndex == to.PendingAsyncStartIndex);
      Debug.Assert(Impl.InParams.Count == to.Impl.InParams.Count);
      Debug.Assert(Impl.OutParams.Count <= to.Impl.OutParams.Count);

      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < Impl.InParams.Count; i++)
      {
        map[Impl.InParams[i]] = Expr.Ident(to.Impl.InParams[i]);
      }
      for (int i = 0; i < PendingAsyncStartIndex; i++)
      {
        map[Impl.OutParams[i]] = Expr.Ident(to.Impl.OutParams[i]);
      }
      for (int i = PendingAsyncStartIndex; i < Impl.OutParams.Count; i++)
      {
        var formal = Impl.OutParams[i];
        var pendingAsyncType = (CtorType)((MapType)formal.TypedIdent.Type).Arguments[0];
        map[formal] = Expr.Ident(to.PAs(pendingAsyncType));
      }
      return Substituter.SubstitutionFromDictionary(map);
    }

    public static Implementation CreateDuplicateImplementation(Implementation impl, string name)
    {
      var duplicateImpl = new Duplicator().VisitImplementation(impl);
      var proc = duplicateImpl.Proc;
      duplicateImpl.Name = name;
      duplicateImpl.Attributes = null;
      // in case impl.Proc is ActionDecl, convert to Procedure
      duplicateImpl.Proc = new Procedure(proc.tok, name, proc.TypeParameters, proc.InParams,
        proc.OutParams, proc.IsPure, new List<Requires>(), proc.Modifies, new List<Ensures>());
      CivlUtil.AddInlineAttribute(duplicateImpl.Proc);
      return duplicateImpl;
    }

    public static void AddGateSufficiencyCheckers(CivlTypeChecker civlTypeChecker, List<Declaration> decls)
    {
      decls.AddRange(gateSufficiencyCheckerDecls);
    }

    private static List<Declaration> gateSufficiencyCheckerDecls = new List<Declaration>();

    private void AddGateSufficiencyCheckerAndHoistAsserts(CivlTypeChecker civlTypeChecker)
    {
      if (ActionDecl.Asserts.Count == 0)
      {
        Gate = HoistAsserts(Impl, civlTypeChecker.Options);
        return;
      }

      var gateSubst = Substituter.SubstitutionFromDictionary(ActionDecl.InParams
            .Zip(Impl.InParams)
            .ToDictionary(x => x.Item1, x => (Expr)Expr.Ident(x.Item2)));

      var checkerName = $"{Name}_GateSufficiencyChecker";
      var checkerImpl = new Duplicator().VisitImplementation(Impl);
      checkerImpl.Name = checkerName;
      checkerImpl.Attributes = null;
      var requires = ActionDecl.Asserts.Select(
        assertCmd => new Requires(assertCmd.tok, false, Substituter.Apply(gateSubst, assertCmd.Expr),
                                null, CivlAttributes.ApplySubstitutionToPoolHints(gateSubst, assertCmd.Attributes))).ToList();
      var proc = checkerImpl.Proc;
      checkerImpl.Proc = new Procedure(proc.tok, checkerName, proc.TypeParameters, proc.InParams,
        proc.OutParams, proc.IsPure, requires, proc.Modifies, new List<Ensures>());
      gateSufficiencyCheckerDecls.AddRange(new Declaration[] { checkerImpl.Proc, checkerImpl });

      HoistAsserts(Impl, civlTypeChecker.Options);
      
      Gate = ActionDecl.Asserts.Select(
        assertCmd => new AssertCmd(assertCmd.tok, Substituter.Apply(gateSubst, assertCmd.Expr),
                                  CivlAttributes.ApplySubstitutionToPoolHints(gateSubst, assertCmd.Attributes))).ToList();
    }

    private Function ComputeInputOutputRelation(CivlTypeChecker civlTypeChecker, Implementation impl)
    {
      var alwaysMap = new Dictionary<Variable, Expr>();
      var foroldMap = new Dictionary<Variable, Expr>();
      civlTypeChecker.program.GlobalVariables.ForEach(g =>
      {
        alwaysMap[g] = Expr.Ident(civlTypeChecker.BoundVariable(g.Name, g.TypedIdent.Type));
        foroldMap[g] = Expr.Ident(civlTypeChecker.BoundVariable($"old_{g.Name}", g.TypedIdent.Type));
      });
      impl.InParams.Concat(impl.OutParams).ForEach(v =>
      {
        alwaysMap[v] = Expr.Ident(VarHelper.Formal(v.Name, v.TypedIdent.Type, true));
      });
      var always = Substituter.SubstitutionFromDictionary(alwaysMap);
      var forold = Substituter.SubstitutionFromDictionary(foroldMap);
      var transitionRelationExpr =
        Substituter.ApplyReplacingOldExprs(always, forold,
          TransitionRelationComputation.Refinement(civlTypeChecker, impl, new HashSet<Variable>(ModifiedGlobalVars)));
      var gateExprs = Gate.Select(assertCmd =>
        Substituter.ApplyReplacingOldExprs(always, forold, ExprHelper.Old(assertCmd.Expr)));
      var transitionRelationInputs = impl.InParams.Concat(impl.OutParams)
        .Select(key => alwaysMap[key]).OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
      var inputOutputRelation = new Function(Token.NoToken, $"Civl_InputOutputRelation_{impl.Name}",
        new List<TypeVariable>(),
        transitionRelationInputs, VarHelper.Formal(TypedIdent.NoName, Type.Bool, false), null,
        new QKeyValue(Token.NoToken, "inline", new List<object>(), null));
      var existsVars = foroldMap.Values
        .Concat(alwaysMap.Keys.Where(key => key is GlobalVariable).Select(key => alwaysMap[key]))
        .OfType<IdentifierExpr>().Select(ie => ie.Decl).ToList();
      var expr = Expr.And(gateExprs.Append(transitionRelationExpr));
      inputOutputRelation.Body = existsVars.Any() ? ExprHelper.ExistsExpr(existsVars, expr) : expr;
      CivlUtil.ResolveAndTypecheck(civlTypeChecker.Options, inputOutputRelation.Body);
      return inputOutputRelation;
    }

    public static void DesugarCreateAsyncs(CivlTypeChecker civlTypeChecker, Implementation impl, ActionDecl actionDecl)
    {
      Debug.Assert(impl.OutParams.Count == actionDecl.OutParams.Count);
      var pendingAsyncTypeToActionDecl = new Dictionary<CtorType, ActionDecl>();
      var lhss = new List<IdentifierExpr>();
      var rhss = new List<Expr>();
      actionDecl.CreateActionDecls.ForEach(decl =>
      {
        pendingAsyncTypeToActionDecl[decl.PendingAsyncType] = decl;
        var pa = civlTypeChecker.Formal($"PAs_{decl.Name}", decl.PendingAsyncMultisetType, false);
        impl.Proc.OutParams.Add(pa);
        impl.OutParams.Add(pa);
        lhss.Add(Expr.Ident(pa));
        rhss.Add(ExprHelper.FunctionCall(decl.PendingAsyncConst, Expr.Literal(0)));
      });
      var tc = new TypecheckingContext(null, civlTypeChecker.Options);
      var initAssignCmd = CmdHelper.AssignCmd(lhss, rhss);
      initAssignCmd.Typecheck(tc);
      impl.Blocks[0].Cmds.Insert(0, initAssignCmd);
      impl.Blocks.ForEach(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var originalProc = (Procedure)Monomorphizer.GetOriginalDecl(callCmd.Proc);
            if (callCmd.IsAsync)
            {
              var actionDecl = (ActionDecl)callCmd.Proc;
              var pendingAsyncMultiset = 
                Expr.Store(
                  ExprHelper.FunctionCall(actionDecl.PendingAsyncConst, Expr.Literal(0)),
                  ExprHelper.FunctionCall(actionDecl.PendingAsyncCtor, callCmd.Ins),
                  Expr.Literal(1));
              var pendingAsyncMultisetType = TypeHelper.MapType(actionDecl.PendingAsyncType, Type.Int);
              var pendingAsyncCollector = impl.OutParams.Skip(actionDecl.OutParams.Count).First(v => v.TypedIdent.Type.Equals(pendingAsyncMultisetType));
              var updateAssignCmd = CmdHelper.AssignCmd(pendingAsyncCollector,
                ExprHelper.FunctionCall(actionDecl.PendingAsyncAdd, Expr.Ident(pendingAsyncCollector), pendingAsyncMultiset));
              updateAssignCmd.Typecheck(tc);
              newCmds.Add(updateAssignCmd);
              continue;
            }
            else if (originalProc.Name == "create_asyncs" || originalProc.Name == "create_multi_asyncs")
            {
              var pendingAsyncType =
                (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
              var pendingAsync = pendingAsyncTypeToActionDecl[pendingAsyncType];
              var pendingAsyncMultiset = originalProc.Name == "create_asyncs"
                  ? ExprHelper.FunctionCall(pendingAsync.PendingAsyncIte, callCmd.Ins[0],
                    ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(1)),
                    ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(0)))
                  : callCmd.Ins[0];
              var pendingAsyncMultisetType = TypeHelper.MapType(pendingAsyncType, Type.Int);
              var pendingAsyncCollector = impl.OutParams.Skip(actionDecl.OutParams.Count).First(v => v.TypedIdent.Type.Equals(pendingAsyncMultisetType));
              var updateAssignCmd = CmdHelper.AssignCmd(pendingAsyncCollector,
                ExprHelper.FunctionCall(pendingAsync.PendingAsyncAdd, Expr.Ident(pendingAsyncCollector), pendingAsyncMultiset));
              updateAssignCmd.Typecheck(tc);
              newCmds.Add(updateAssignCmd);
              continue;
            }
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      });
    }

    private void DropSetChoice(Implementation impl)
    {
      impl.Blocks.ForEach(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var originalProcName = Monomorphizer.GetOriginalDecl(callCmd.Proc).Name;
            if (originalProcName == "set_choice")
            {
              continue;
            }
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      });
    }

    private void DesugarSetChoice(CivlTypeChecker civlTypeChecker, Implementation impl)
    {
      var choice = civlTypeChecker.Formal("choice", TypeHelper.CtorType(ChoiceDatatypeTypeCtorDecl), false);
      impl.Proc.OutParams.Add(choice);
      impl.OutParams.Add(choice);
      impl.Blocks.ForEach(block =>
      {
        var newCmds = new List<Cmd>();
        foreach (var cmd in block.Cmds)
        {
          if (cmd is CallCmd callCmd)
          {
            var originalProcName = Monomorphizer.GetOriginalDecl(callCmd.Proc).Name;
            if (originalProcName == "set_choice")
            {
              var pendingAsyncType = (CtorType)civlTypeChecker.program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
              var pendingAsync = PendingAsyncs.First(decl => decl.PendingAsyncType.Equals(pendingAsyncType));
              var tc = new TypecheckingContext(null, civlTypeChecker.Options);
              var emptyExpr = Expr.Eq(Expr.Ident(PAs(pendingAsyncType)),
                ExprHelper.FunctionCall(pendingAsync.PendingAsyncConst, Expr.Literal(0)));
              var memberExpr = Expr.Gt(Expr.Select(Expr.Ident(PAs(pendingAsyncType)), callCmd.Ins[0]),
                Expr.Literal(0));
              var assertCmd = CmdHelper.AssertCmd(cmd.tok, Expr.Or(emptyExpr, memberExpr),
                "Choice is not a created pending async");
              assertCmd.Typecheck(tc);
              newCmds.Add(assertCmd);
              var assignCmd = CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(Expr.Ident(choice), pendingAsyncType.Decl.Name), callCmd.Ins[0]);
              assignCmd.Typecheck(tc);
              newCmds.Add(assignCmd);
              continue;
            }
          }
          newCmds.Add(cmd);
        }
        block.Cmds = newCmds;
      });
    }

    /*
     * HoistAsserts computes the weakest liberal precondition (wlp) of the body
     * of impl as a collection of AssertCmd's. As a side effect, all AssertCmd's
     * in any block of impl are removed.
     *
     * HoistAsserts assumes that the body of impl does not contain any loops or
     * calls. The blocks in impl are sorted from entry to exit and processed in
     * reverse order, thus ensuring that a block is processed only once the wlp
     * of all its successors has been computed.
     */
    private List<AssertCmd> HoistAsserts(Implementation impl, ConcurrencyOptions options)
    {
      Dictionary<Block, List<AssertCmd>> wlps = new Dictionary<Block, List<AssertCmd>>();
      Graph<Block> dag = Program.GraphFromBlocks(impl.Blocks, false);
      foreach (var block in dag.TopologicalSort())
      {
        if (block.TransferCmd is ReturnCmd)
        {
          var wlp = HoistAsserts(block.Cmds, new List<AssertCmd>(), options);
          wlps.Add(block, wlp);
        }
        else if (block.TransferCmd is GotoCmd gotoCmd)
        {
          var wlp =
            HoistAsserts(block.Cmds, gotoCmd.labelTargets.SelectMany(b => wlps[b]).ToList(), options);
          wlps.Add(block, wlp);
        }
        else
        {
          throw new Cce.UnreachableException();
        }
      }
      return wlps[impl.Blocks[0]].Select(assertCmd => Forall(impl.LocVars.Union(impl.OutParams), assertCmd)).ToList();
    }

    private List<AssertCmd> HoistAsserts(List<Cmd> cmds, List<AssertCmd> postconditions, ConcurrencyOptions options)
    {
      for (int i = cmds.Count - 1; i >= 0; i--)
      {
        var cmd = cmds[i];
        if (cmd is AssertCmd assertCmd)
        {
          postconditions.Add(assertCmd);
        } 
        else if (cmd is AssumeCmd assumeCmd)
        {
          postconditions = postconditions
            .Select(assertCmd => new AssertCmd(assertCmd.tok, Expr.Imp(assumeCmd.Expr, assertCmd.Expr))).ToList();
        }
        else if (cmd is AssignCmd assignCmd)
        {
          var varToExpr = new Dictionary<Variable, Expr>();
          var simpleAssignCmd = assignCmd.AsSimpleAssignCmd;
          for (var j = 0; j < simpleAssignCmd.Lhss.Count; j++)
          {
            var lhs = simpleAssignCmd.Lhss[j];
            var rhs = simpleAssignCmd.Rhss[j];
            varToExpr.Add(lhs.DeepAssignedVariable, rhs);
          }
          postconditions = postconditions.Select(assertCmd =>
            new AssertCmd(assertCmd.tok, SubstitutionHelper.Apply(varToExpr, assertCmd.Expr))).ToList();
        }
        else if (cmd is HavocCmd havocCmd)
        {
          postconditions = postconditions.Select(assertCmd => Forall(havocCmd.Vars.Select(ie => ie.Decl), assertCmd))
            .ToList();
        }
        else if (cmd is UnpackCmd unpackCmd)
        {
          var desugaredCmd = (StateCmd) unpackCmd.GetDesugaring(options);
          postconditions = HoistAsserts(desugaredCmd.Cmds, postconditions, options); // removes precondition assert from desugaredCmd.Cmds
        }
        else
        {
          throw new Cce.UnreachableException();
        }
      }
      cmds.RemoveAll(cmd => cmd is AssertCmd);
      return postconditions;
    }
    
    private static AssertCmd Forall(IEnumerable<Variable> vars, AssertCmd assertCmd)
    {
      var freeObjects = new GSet<object>();
      assertCmd.Expr.ComputeFreeVariables(freeObjects);
      var quantifiedVars = freeObjects.OfType<Variable>().Intersect(vars);
      if (quantifiedVars.Count() == 0)
      {
        return assertCmd;
      }
      var varMapping = quantifiedVars.ToDictionary(v => v,
        v => (Variable) VarHelper.BoundVariable(v.Name, v.TypedIdent.Type));
      return new AssertCmd(assertCmd.tok,
        ExprHelper.ForallExpr(varMapping.Values.ToList(), SubstitutionHelper.Apply(varMapping, assertCmd.Expr)));
    }
    
    private void DeclareTriggerFunctions()
    {
      TriggerFunctions = new Dictionary<Variable, Function>();
      foreach (var v in Impl.LocVars)
      {
        List<Variable> args = new List<Variable> {VarHelper.Formal(v.Name, v.TypedIdent.Type, true)};
        Variable result = VarHelper.Formal("r", Type.Bool, false);
        TriggerFunctions[v] = new Function(Token.NoToken, $"Trigger_{Impl.Name}_{v.Name}", args, result);
      }

      for (int i = 0; i < Impl.LocVars.Count; i++)
      {
        TriggerFunctions[FirstImpl.LocVars[i]] = TriggerFunctions[Impl.LocVars[i]];
        TriggerFunctions[SecondImpl.LocVars[i]] = TriggerFunctions[Impl.LocVars[i]];
      }
    }

    /*
     * This method adds triggers for each local variable at the beginning of the atomic
     * action and after every havoc of the variable.
     * As an optimization, the injection of the trigger is performed only if the variable
     * is live at the point of injection.
     */
    public void AddTriggerAssumes(Program program, ConcurrencyOptions options)
    {
      var liveVariableAnalysis = new AtomicActionLiveVariableAnalysis(Impl, options);
      liveVariableAnalysis.Compute();
      foreach (Variable v in Impl.LocVars)
      {
        var f = TriggerFunctions[v];
        program.AddTopLevelDeclaration(f);
        if (liveVariableAnalysis.IsLiveBefore(v, Impl.Blocks[0]))
        {
          var assume = CmdHelper.AssumeCmd(ExprHelper.FunctionCall(f, Expr.Ident(v)));
          Impl.Blocks[0].Cmds.Insert(0, assume);
        }
      }
      Impl.Blocks.ForEach(block =>
      {
        block.Cmds = block.Cmds.SelectMany(cmd =>
        {
          var newCmds = new List<Cmd> { cmd };
          if (cmd is HavocCmd havocCmd)
          {
            var liveHavocVars = new HashSet<Variable>(havocCmd.Vars.Select(x => x.Decl)
              .Where(v => liveVariableAnalysis.IsLiveAfter(v, havocCmd)));
            Impl.LocVars.Intersect(liveHavocVars).ForEach(v =>
            {
              newCmds.Add(CmdHelper.AssumeCmd(ExprHelper.FunctionCall(TriggerFunctions[v], Expr.Ident(v))));
            });
          }
          return newCmds;
        }).ToList();
      });
    }
  }

  /// <summary>
  /// Creates first/second copies of atomic actions used in commutativity checks
  /// (i.e., all non-global variables are prefixed with first_ resp. second_).
  /// Note that we also rename bound variables.
  /// </summary>
  class AtomicActionDuplicator : Duplicator
  {
    private readonly string prefix;
    private Dictionary<Variable, Expr> subst;
    private Dictionary<Variable, Expr> bound;
    private List<Variable> inParamsCopy;
    private List<Variable> outParamsCopy;
    private List<Variable> localsCopy;

    public static void SetupCopy(Action action, ref List<AssertCmd> gateCopy, ref Implementation implCopy,
      string prefix)
    {
      var aad = new AtomicActionDuplicator(prefix, action);

      gateCopy = new List<AssertCmd>();
      foreach (AssertCmd assertCmd in action.Gate)
      {
        gateCopy.Add((AssertCmd) aad.Visit(assertCmd));
      }

      implCopy = aad.VisitImplementation(action.Impl);
    }

    private AtomicActionDuplicator(string prefix, Action action)
    {
      this.prefix = prefix;
      subst = new Dictionary<Variable, Expr>();
      bound = new Dictionary<Variable, Expr>();

      inParamsCopy = new List<Variable>();
      outParamsCopy = new List<Variable>();
      localsCopy = new List<Variable>();


      foreach (Variable x in action.Impl.InParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          true, x.Attributes);
        inParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.Impl.OutParams)
      {
        Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          false, x.Attributes);
        outParamsCopy.Add(xCopy);
        subst[x] = Expr.Ident(xCopy);
      }

      foreach (Variable x in action.Impl.LocVars)
      {
        Variable xCopy = new LocalVariable(Token.NoToken,
          new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), x.Attributes);
        subst[x] = Expr.Ident(xCopy);
        localsCopy.Add(xCopy);
      }
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      node = base.VisitImplementation(node);
      node.InParams = inParamsCopy;
      node.OutParams = outParamsCopy;
      node.LocVars = localsCopy;
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (subst.ContainsKey(node.Decl))
      {
        return subst[node.Decl];
      }
      else if (bound.ContainsKey(node.Decl))
      {
        return bound[node.Decl];
      }

      return base.VisitIdentifierExpr(node);
    }

    public override BinderExpr VisitBinderExpr(BinderExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          x.Attributes));

      foreach (var x in node.Dummies)
      {
        bound.Add(x, Expr.Ident(oldToNew[x]));
      }

      var expr = (BinderExpr)base.VisitBinderExpr(node);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

      // We process triggers of quantifier expressions here, because otherwise the
      // substitutions for bound variables have to be leaked outside this procedure.
      if (node is QuantifierExpr quantifierExpr)
      {
        if (quantifierExpr.Triggers != null)
        {
          ((QuantifierExpr) expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
        }
      }

      foreach (var x in node.Dummies)
      {
        bound.Remove(x);
      }

      return expr;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
      return (QuantifierExpr) this.VisitBinderExpr(node);
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      var retNode = (UnpackCmd)base.VisitUnpackCmd(node);
      retNode.ResetDesugaring();
      return retNode;
    }
  }
}