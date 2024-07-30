using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
  public class YieldingProcDuplicator : Duplicator
  {
    /* This class creates duplicate copies of yielding procedures for a particular layer
     * rewriting calls to procedures that have been converted to atomic actions. 
     * Async calls are also rewritten so that the resulting copies are guaranteed not to
     * have any async calls.  The copy of yielding procedure X shares local variables of X.
     * This sharing is exploited when instrumenting the duplicates in the class
     * YieldProcInstrumentation.
     */
    private CivlTypeChecker civlTypeChecker;
    private int layerNum;

    private Dictionary<Procedure, Procedure> procToDuplicate; /* Original -> Duplicate */
    private AbsyMap absyMap; /* Duplicate -> Original */
    private Dictionary<string, Procedure> asyncCallPreconditionCheckers;

    private Dictionary<CallCmd, CallCmd> refinementCallCmds; // rewritten -> original
    private Dictionary<CallCmd, Block> refinementBlocks; // rewritten -> block

    private LinearRewriter linearRewriter;

    private ConcurrencyOptions Options => civlTypeChecker.Options;

    public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, int layerNum)
    {
      this.civlTypeChecker = civlTypeChecker;
      this.layerNum = layerNum;
      this.procToDuplicate = new Dictionary<Procedure, Procedure>();
      this.absyMap = new AbsyMap();
      this.asyncCallPreconditionCheckers = new Dictionary<string, Procedure>();
      this.refinementBlocks = new Dictionary<CallCmd, Block>();
      this.linearRewriter = new LinearRewriter(civlTypeChecker);
    }

    #region Procedure duplication

    public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
    {
      if (!procToDuplicate.ContainsKey(node))
      {
        Debug.Assert(layerNum <= node.Layer);
        var proc = new Procedure(
          node.tok,
          civlTypeChecker.AddNamePrefix($"{node.Name}_{layerNum}"),
          new List<TypeVariable>(),
          VisitVariableSeq(node.InParams),
          VisitVariableSeq(node.OutParams),
          false,
          VisitRequiresSeq(node.Requires),
          (node.HasMoverType && node.Layer == layerNum
            ? node.ModifiedVars.Select(g => Expr.Ident(g))
            : civlTypeChecker.GlobalVariables.Select(v => Expr.Ident(v))).ToList(),
          VisitEnsuresSeq(node.Ensures));
        procToDuplicate[node] = proc;
        absyMap[proc] = node;
      }
      return procToDuplicate[node];
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      requiresSeq = base.VisitRequiresSeq(requiresSeq);
      requiresSeq.RemoveAll(req => req.Condition.Equals(Expr.True));
      return requiresSeq;
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      ensuresSeq = base.VisitEnsuresSeq(ensuresSeq);
      ensuresSeq.RemoveAll(ens => ens.Condition.Equals(Expr.True));
      return ensuresSeq;
    }

    public override Requires VisitRequires(Requires node)
    {
      Requires requires = base.VisitRequires(node);
      if (node.Free)
      {
        return requires;
      }
      
      if (!node.Layers.Contains(layerNum))
      {
        requires.Condition = Expr.True;
      }

      return requires;
    }

    public override Ensures VisitEnsures(Ensures node)
    {
      Ensures ensures = base.VisitEnsures(node);
      if (node.Free)
      {
        return ensures;
      }
      
      if (!node.Layers.Contains(layerNum))
      {
        ensures.Condition = Expr.True;
      }

      return ensures;
    }

    #endregion

    #region Implementation duplication

    private Implementation enclosingImpl;
    private YieldProcedureDecl enclosingYieldingProc;
    private bool IsRefinementLayer => layerNum == enclosingYieldingProc.Layer;

    private Action RefinedAction => civlTypeChecker.Action(enclosingYieldingProc.RefinedAction.ActionDecl);

    private List<Cmd> newCmdSeq;

    private Dictionary<CtorType, Variable> returnedPAs;

    private Variable ReturnedPAs(CtorType pendingAsyncType)
    {
      if (!returnedPAs.ContainsKey(pendingAsyncType))
      {
        returnedPAs[pendingAsyncType] = civlTypeChecker.LocalVariable($"returnedPAs_{pendingAsyncType.Decl.Name}",
          TypeHelper.MapType(pendingAsyncType, Type.Int));
      }
      return returnedPAs[pendingAsyncType];
    }

    private Variable CollectedPAs(CtorType pendingAsyncType)
    {
      if (!civlTypeChecker.PendingAsyncCollectors(enclosingImpl).TryGetValue(pendingAsyncType, out var collectedPAs))
      {
        collectedPAs = civlTypeChecker.LocalVariable($"collectedPAs_{pendingAsyncType.Decl.Name}",
          TypeHelper.MapType(pendingAsyncType, Type.Int));
        civlTypeChecker.PendingAsyncCollectors(enclosingImpl)[pendingAsyncType] = collectedPAs;
      }
      return collectedPAs;
    }

    public override Implementation VisitImplementation(Implementation impl)
    {
      enclosingYieldingProc = (YieldProcedureDecl)impl.Proc;
      enclosingImpl = impl;
      Debug.Assert(layerNum <= enclosingYieldingProc.Layer);

      returnedPAs = new Dictionary<CtorType, Variable>();

      refinementCallCmds = new Dictionary<CallCmd, CallCmd>();
      Implementation newImpl = base.VisitImplementation(impl);
      newImpl.Name = newImpl.Proc.Name;

      foreach (var kv in refinementCallCmds)
      {
        var rewrittenCallCmd = kv.Key;
        var originalCallCmd = kv.Value;
        newCmdSeq = new List<Cmd>();
        AddActionCall(originalCallCmd, (YieldProcedureDecl)originalCallCmd.Proc);
        var block = BlockHelper.Block(
          civlTypeChecker.AddNamePrefix($"call_refinement_{refinementBlocks.Count}"),
          newCmdSeq,
          new List<Block>());
        refinementBlocks.Add(rewrittenCallCmd, block);
        newCmdSeq = null;
      }

      refinementCallCmds = null;
      
      newImpl.LocVars.AddRange(returnedPAs.Values);

      if (!enclosingYieldingProc.HasMoverType && RefinedAction.HasPendingAsyncs && IsRefinementLayer)
      {
        var assumeExpr = EmptyPendingAsyncMultisetExpr(CollectedPAs, RefinedAction.PendingAsyncs);
        newImpl.LocVars.AddRange(civlTypeChecker.PendingAsyncCollectors(impl).Values.Except(impl.LocVars));
        newImpl.Blocks.First().Cmds.Insert(0, CmdHelper.AssumeCmd(assumeExpr));
      }

      absyMap[newImpl] = impl;
      return newImpl;
    }

    public override Block VisitBlock(Block node)
    {
      var block = base.VisitBlock(node);
      absyMap[block] = node;
      return block;
    }

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      var assertCmd = (AssertCmd) base.VisitAssertCmd(node);
      if (!node.Layers.Contains(layerNum))
      {
        assertCmd.Expr = Expr.True;
      }
      return assertCmd;
    }

    public override Cmd VisitCallCmd(CallCmd call)
    {
      var newCall = (CallCmd) base.VisitCallCmd(call);
      absyMap[newCall] = call;
      return newCall;
    }

    public override Cmd VisitParCallCmd(ParCallCmd parCall)
    {
      var newParCall = (ParCallCmd) base.VisitParCallCmd(parCall);
      absyMap[newParCall] = parCall;
      foreach (var newCall in newParCall.CallCmds)
      {
        absyMap[newCall] = parCall;
      }

      return newParCall;
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      newCmdSeq = new List<Cmd>();
      foreach (var cmd in cmdSeq)
      {
        Cmd newCmd = (Cmd) Visit(cmd);

        if (newCmd is CallCmd)
        {
          ProcessCallCmd((CallCmd) newCmd);
        }
        else if (newCmd is ParCallCmd)
        {
          ProcessParCallCmd((ParCallCmd) newCmd);
        }
        else
        {
          newCmdSeq.Add(newCmd);
        }
      }
      return newCmdSeq;
    }

    private void ProcessCallCmd(CallCmd newCall)
    {
      if (newCall.Proc.IsPure)
      {
        var callLayerRange = newCall.LayerRange;
        if (callLayerRange.Contains(layerNum))
        {
          if (newCall.Proc is ActionDecl actionDecl)
          {
            var pureAction = civlTypeChecker.Action(actionDecl);
            newCall.Proc = pureAction.Impl.Proc;
            InjectGate(pureAction, newCall);
            newCmdSeq.Add(newCall);
          }
          else if (LinearRewriter.IsPrimitive(newCall.Proc))
          {
            newCmdSeq.AddRange(linearRewriter.RewriteCallCmd(newCall));
          }
          else
          {
            newCmdSeq.Add(newCall);
          }
        }
        return;
      }

      if (newCall.Proc is YieldInvariantDecl yieldInvariant)
      {
        if (layerNum == yieldInvariant.Layer)
        {
          var parCallCmd = new ParCallCmd(newCall.tok, new List<CallCmd> {newCall});
          absyMap[parCallCmd] = absyMap[newCall];
          newCmdSeq.Add(parCallCmd);
        }
        return;
      }

      // handle calls to yielding procedures in the rest of this method
      var yieldingProc = (YieldProcedureDecl)newCall.Proc;

      if (newCall.IsAsync)
      {
        if (yieldingProc.Layer < layerNum)
        {
          Debug.Assert(!yieldingProc.HasMoverType);
          if (newCall.HasAttribute(CivlAttributes.SYNC))
          {
            // synchronize the called atomic action
            AddActionCall(newCall, yieldingProc);
          }
          else if (IsRefinementLayer)
          {
            if (newCall.HasAttribute(CivlAttributes.SKIP))
            {
              var calleeRefinedAction = PrepareNewCall(newCall, yieldingProc);
              InjectGate(calleeRefinedAction, newCall);
            }
            else
            {
              AddPendingAsync(newCall, yieldingProc);
            }
          }
        }
        else
        {
          if (yieldingProc.HasMoverType && yieldingProc.Layer == layerNum)
          {
            // synchronize the called mover procedure
            AddDuplicateCall(newCall, false);
          }
          else
          {
            DesugarAsyncCall(newCall);
            if (IsRefinementLayer)
            {
              Debug.Assert(!yieldingProc.HasMoverType);
              AddPendingAsync(newCall, yieldingProc);
            }
          }
        }
        return;
      }

      // handle synchronous calls to yielding procedures
      if (yieldingProc.HasMoverType)
      {
        AddDuplicateCall(newCall, yieldingProc.Layer > layerNum);
      }
      else if (!yieldingProc.HasMoverType)
      {
        if (yieldingProc.Layer < layerNum)
        {
          AddActionCall(newCall, yieldingProc);
        }
        else
        {
          if (IsRefinementLayer && layerNum == yieldingProc.Layer && yieldingProc.RefinedAction != null)
          {
            refinementCallCmds[newCall] = (CallCmd) VisitCallCmd(newCall);
          }

          AddDuplicateCall(newCall, true);
        }

        Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count);
      }
      else
      {
        Debug.Assert(false);
      }
    }

    private void ProcessParCallCmd(ParCallCmd newParCall)
    {
      var callCmds = new List<CallCmd>();
      foreach (var callCmd in newParCall.CallCmds)
      {
        if (callCmd.Proc is YieldProcedureDecl)
        {
          var yieldingProc = (YieldProcedureDecl)callCmd.Proc;
          if (layerNum > yieldingProc.Layer && !yieldingProc.HasMoverType ||
              layerNum == yieldingProc.Layer && yieldingProc.HasMoverType)
          {
            if (callCmds.Count > 0)
            {
              var parCallCmd = new ParCallCmd(newParCall.tok, callCmds);
              absyMap[parCallCmd] = absyMap[newParCall];
              newCmdSeq.Add(parCallCmd);
              callCmds = new List<CallCmd>();
            }

            ProcessCallCmd(callCmd);
            continue;
          }
        }

        if (procToDuplicate.ContainsKey(callCmd.Proc))
        {
          var yieldingProc = (YieldProcedureDecl)callCmd.Proc;
          if (!yieldingProc.HasMoverType)
          {
            if (IsRefinementLayer && layerNum == yieldingProc.Layer && yieldingProc.RefinedAction != null)
            {
              refinementCallCmds[callCmd] = (CallCmd) VisitCallCmd(callCmd);
            }
          }

          callCmd.Proc = procToDuplicate[callCmd.Proc];
          callCmd.callee = callCmd.Proc.Name;
          callCmds.Add(callCmd);
        }
        else
        {
          var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
          if (layerNum == yieldInvariant.Layer)
          {
            callCmds.Add(callCmd);
          }
        }
      }

      if (callCmds.Count > 0)
      {
        var parCallCmd = new ParCallCmd(newParCall.tok, callCmds);
        absyMap[parCallCmd] = absyMap[newParCall];
        newCmdSeq.Add(parCallCmd);
      }
    }

    private Action PrepareNewCall(CallCmd newCall, YieldProcedureDecl calleeActionProc)
    {
      var calleeRefinedAction = civlTypeChecker.Action(calleeActionProc.RefinedActionAtLayer(layerNum));

      newCall.IsAsync = false;
      newCall.Proc = calleeRefinedAction.Impl.Proc;
      newCall.callee = newCall.Proc.Name;

      // We drop the hidden parameters of the procedure from the call to the action.
      Debug.Assert(newCall.Ins.Count == calleeActionProc.InParams.Count);
      Debug.Assert(newCall.Outs.Count == calleeActionProc.OutParams.Count);
      var newIns = new List<Expr>();
      var newOuts = new List<IdentifierExpr>();
      for (int i = 0; i < calleeActionProc.InParams.Count; i++)
      {
        if (calleeActionProc.VisibleFormals.Contains(calleeActionProc.InParams[i]))
        {
          newIns.Add(newCall.Ins[i]);
        }
      }

      for (int i = 0; i < calleeActionProc.OutParams.Count; i++)
      {
        if (calleeActionProc.VisibleFormals.Contains(calleeActionProc.OutParams[i]))
        {
          newOuts.Add(newCall.Outs[i]);
        }
      }

      newCall.Ins = newIns;
      newCall.Outs = newOuts;

      return calleeRefinedAction;
    }

    private void AddActionCall(CallCmd newCall, YieldProcedureDecl calleeActionProc)
    {
      var calleeRefinedAction = PrepareNewCall(newCall, calleeActionProc);
      InjectGate(calleeRefinedAction, newCall, !IsRefinementLayer);
      newCmdSeq.Add(newCall);

      if (calleeRefinedAction.HasPendingAsyncs)
      {
        Debug.Assert(newCall.Outs.Count == newCall.Proc.OutParams.Count - calleeRefinedAction.PendingAsyncs.Count());
        CollectReturnedPendingAsyncs(newCall, calleeRefinedAction);
      }
    }

    private void InjectGate(Action action, CallCmd callCmd, bool assume = false)
    {
      if (action.Gate.Count == 0)
      {
        return;
      }

      Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
      for (int i = 0; i < action.Impl.InParams.Count; i++)
      {
        // Parameters come from the implementation that defines the action
        map[action.Impl.InParams[i]] = callCmd.Ins[i];
      }

      Substitution subst = Substituter.SubstitutionFromDictionary(map);

      // Important: Do not remove CommentCmd!
      // It separates the injected gate from yield assertions.
      newCmdSeq.Add(new CommentCmd("<<< injected gate"));
      foreach (AssertCmd assertCmd in action.Gate)
      {
        var expr = Substituter.Apply(subst, assertCmd.Expr);
        if (assume)
        {
          newCmdSeq.Add(new AssumeCmd(assertCmd.tok, expr));
        }
        else
        {
          newCmdSeq.Add(CmdHelper.AssertCmd(assertCmd.tok, expr,
            $"this gate of {action.Name} could not be proved"));
        }
      }

      newCmdSeq.Add(new CommentCmd("injected gate >>>"));
    }

    private void CollectReturnedPendingAsyncs(CallCmd newCall, Action calleeRefinedAction)
    {
      // Inject pending async collection
      newCall.Outs.AddRange(calleeRefinedAction.PendingAsyncs.Select(decl => Expr.Ident(ReturnedPAs(decl.PendingAsyncType))));
      if (!IsRefinementLayer)
      {
        return;
      }

      calleeRefinedAction.PendingAsyncs.ForEach(decl =>
      {
        if (RefinedAction.PendingAsyncs.Contains(decl))
        {
          newCmdSeq.Add(CmdHelper.AssignCmd(CollectedPAs(decl.PendingAsyncType),
            ExprHelper.FunctionCall(decl.PendingAsyncAdd, Expr.Ident(CollectedPAs(decl.PendingAsyncType)),
              Expr.Ident(ReturnedPAs(decl.PendingAsyncType)))));
        }
        else
        {
          newCmdSeq.Add(CmdHelper.AssertCmd(newCall.tok,
            Expr.Eq(Expr.Ident(ReturnedPAs(decl.PendingAsyncType)), ExprHelper.FunctionCall(decl.PendingAsyncConst, Expr.Literal(0))),
            $"Pending asyncs to action {decl.Name} created by this call are not summarized"));
        }
      });
    }

    private Expr EmptyPendingAsyncMultisetExpr(Func<CtorType, Variable> pendingAsyncMultisets, IEnumerable<ActionDecl> asyncActions)
    {
      var returnExpr = Expr.And(asyncActions.Select(decl =>
        Expr.Eq(Expr.Ident(pendingAsyncMultisets(decl.PendingAsyncType)),
          ExprHelper.FunctionCall(decl.PendingAsyncConst, Expr.Literal(0)))).ToList());
      returnExpr.Typecheck(new TypecheckingContext(null, civlTypeChecker.Options));
      return returnExpr;
    }

    private void AddDuplicateCall(CallCmd newCall, bool makeParallel)
    {
      newCall.IsAsync = false;
      newCall.Proc = procToDuplicate[newCall.Proc];
      newCall.callee = newCall.Proc.Name;
      if (makeParallel)
      {
        var parCallCmd = new ParCallCmd(newCall.tok, new List<CallCmd> {newCall});
        absyMap[parCallCmd] = absyMap[newCall];
        newCmdSeq.Add(parCallCmd);
      }
      else
      {
        newCmdSeq.Add(newCall);
      }
    }

    private void DesugarAsyncCall(CallCmd newCall)
    {
      if (!asyncCallPreconditionCheckers.ContainsKey(newCall.Proc.Name))
      {
        asyncCallPreconditionCheckers[newCall.Proc.Name] = DeclHelper.Procedure(
          civlTypeChecker.AddNamePrefix($"AsyncCall_{newCall.Proc.Name}_{layerNum}"),
          newCall.Proc.InParams, newCall.Proc.OutParams,
          procToDuplicate[newCall.Proc].Requires, new List<IdentifierExpr>(), new List<Ensures>());
      }

      var asyncCallPreconditionChecker = asyncCallPreconditionCheckers[newCall.Proc.Name];
      newCall.IsAsync = false;
      newCall.Proc = asyncCallPreconditionChecker;
      newCall.callee = newCall.Proc.Name;
      newCmdSeq.Add(newCall);
    }

    private void AddPendingAsync(CallCmd newCall, YieldProcedureDecl calleeProc)
    {
      if (calleeProc.RefinedAction.ActionDecl == civlTypeChecker.SkipActionDecl)
      {
        return;
      }
      var calleeRefinedAction = calleeProc.Layer == enclosingYieldingProc.Layer
        ? calleeProc.RefinedAction.ActionDecl
        : calleeProc.RefinedActionAtLayer(layerNum);

      if (RefinedAction.PendingAsyncs.Contains(calleeRefinedAction))
      {
        Expr[] newIns = new Expr[calleeRefinedAction.InParams.Count];
        for (int i = 0, j = 0; i < calleeProc.InParams.Count; i++)
        {
          if (calleeProc.VisibleFormals.Contains(calleeProc.InParams[i]))
          {
            newIns[j] = newCall.Ins[i];
            j++;
          }
        }
        var collectedPAs = CollectedPAs(calleeRefinedAction.PendingAsyncType);
        var pa = ExprHelper.FunctionCall(calleeRefinedAction.PendingAsyncCtor, newIns);
        var inc = Expr.Add(Expr.Select(Expr.Ident(collectedPAs), pa), Expr.Literal(1));
        var add = CmdHelper.AssignCmd(collectedPAs, Expr.Store(Expr.Ident(collectedPAs), pa, inc));
        newCmdSeq.Add(add);
      }
      else
      {
        newCmdSeq.Add(CmdHelper.AssertCmd(newCall.tok, Expr.False, "This pending async is not summarized"));
      }
    }

    #endregion

    public List<Declaration> Collect()
    {
      var decls = new List<Declaration>();
      decls.AddRange(procToDuplicate.Values);
      var newImpls = absyMap.Keys.OfType<Implementation>();
      decls.AddRange(newImpls);
      decls.AddRange(asyncCallPreconditionCheckers.Values);
      decls.AddRange(YieldingProcInstrumentation.TransformImplementations(
        civlTypeChecker,
        layerNum,
        absyMap,
        refinementBlocks));
      return decls;
    }
  }

  public class AbsyMap
  {
    private Dictionary<Absy, Absy> absyMap;

    public AbsyMap()
    {
      this.absyMap = new Dictionary<Absy, Absy>();
    }

    public Absy this[Absy absy]
    {
      get { return this.absyMap[absy]; }
      set { this.absyMap[absy] = value; }
    }

    public T Original<T>(T absy) where T : Absy
    {
      return (T)absyMap[absy];
    }

    public T OriginalOrInput<T>(T absy) where T : Absy
    {
      return absyMap.ContainsKey(absy) ? (T)absyMap[absy] : absy;
    }

    public IEnumerable<Absy> Keys
    {
      get { return absyMap.Keys; }
    }

    public bool ContainsKey(Absy key)
    {
      return absyMap.ContainsKey(key);
    }
  }
}