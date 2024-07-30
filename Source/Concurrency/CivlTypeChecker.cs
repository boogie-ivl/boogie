using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class CivlTypeChecker
  {
    public ConcurrencyOptions Options { get; }
    public CheckingContext checkingContext;
    public Program program;
    public LinearTypeChecker linearTypeChecker;
    public List<int> AllRefinementLayers;
    public ActionDecl SkipActionDecl;
    
    private Dictionary<ActionDecl, Action> actionDeclToAction;
    private List<Sequentialization> sequentializations;
    private Dictionary<Implementation, Dictionary<CtorType, Variable>> implToPendingAsyncCollectors;
    private string namePrefix;

    public CivlTypeChecker(ConcurrencyOptions options, Program program)
    {
      this.checkingContext = new CheckingContext(null);
      this.program = program;
      this.Options = options;
      this.linearTypeChecker = new LinearTypeChecker(this);
      var yieldingProcRefinementLayers = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(impl => impl.Proc is YieldProcedureDecl)
        .Select(decl => ((YieldProcedureDecl)decl.Proc).Layer);
      var actionRefinementLayers = program.TopLevelDeclarations.OfType<ActionDecl>()
        .Where(actionDecl => actionDecl.RefinedAction != null)
        .Select(actionDecl => actionDecl.LayerRange.UpperLayer);
      this.AllRefinementLayers = yieldingProcRefinementLayers.Union(actionRefinementLayers)
        .OrderBy(layer => layer).Distinct().ToList();
      
      this.actionDeclToAction = new Dictionary<ActionDecl, Action>();
      this.sequentializations = new List<Sequentialization>();
      this.implToPendingAsyncCollectors = new Dictionary<Implementation, Dictionary<CtorType, Variable>>();

      IEnumerable<string> declNames = program.TopLevelDeclarations.OfType<NamedDeclaration>().Select(x => x.Name);
      IEnumerable<string> localVarNames = VariableNameCollector.Collect(program);
      IEnumerable<string> blockLabels = program.TopLevelDeclarations.OfType<Implementation>()
        .SelectMany(x => x.Blocks.Select(y => y.Label));
      var allNames = declNames.Union(localVarNames).Union(blockLabels);
      namePrefix = "Civl_";
      foreach (var name in allNames)
      {
        while (name.StartsWith(namePrefix))
        {
          namePrefix = namePrefix + "_";
        }
      }

      SkipActionDecl = new ActionDecl(Token.NoToken, AddNamePrefix("Skip"), MoverType.Both, new List<Variable>(),
        new List<Variable>(), true, new List<ActionDeclRef>(), null, null,
        new List<Requires>(), new List<CallCmd>(), new List<AssertCmd>(),
        new List<IdentifierExpr>(), null, null);
      var skipImplementation = DeclHelper.Implementation(
        SkipActionDecl,
        new List<Variable>(),
        new List<Variable>(),
        new List<Variable>(),
        new List<Block> { BlockHelper.Block("init", new List<Cmd>()) });
      SkipActionDecl.LayerRange = LayerRange.MinMax;
      SkipActionDecl.Impl = skipImplementation;
      if (program.TopLevelDeclarations.OfType<YieldProcedureDecl>().Any())
      {
        program.AddTopLevelDeclaration(SkipActionDecl);
        program.AddTopLevelDeclaration(skipImplementation);
      }
      program.TopLevelDeclarations.OfType<YieldProcedureDecl>()
        .Where(decl => !decl.HasMoverType && decl.RefinedAction == null).ForEach(decl =>
        {
          decl.RefinedAction = new ActionDeclRef(Token.NoToken, SkipActionDecl.Name)
          {
            ActionDecl = SkipActionDecl
          };
        });
    }

    public string AddNamePrefix(string name)
    {
      return $"{namePrefix}{name}";
    }
    
    public LocalVariable LocalVariable(string name, Type type)
    {
      return VarHelper.LocalVariable($"{namePrefix}{name}", type);
    }

    public BoundVariable BoundVariable(string name, Type type)
    {
      return VarHelper.BoundVariable($"{namePrefix}{name}", type);
    }

    public Formal Formal(string name, Type type, bool incoming)
    {
      return VarHelper.Formal($"{namePrefix}{name}", type, incoming);
    }

    public void TypeCheck()
    {
      linearTypeChecker.TypeCheck();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }
      
      var actionDecls = TypeCheckActions();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      TypeCheckYieldingProcedures();
      if (checkingContext.ErrorCount > 0)
      {
        return;
      }

      InlineAtomicActions(actionDecls);
      CreateAtomicActions(actionDecls);
      CreateSequentializations(actionDecls);
      AttributeEraser.Erase(this);
      YieldSufficiencyTypeChecker.TypeCheck(this);
    }

    private HashSet<ActionDecl> TypeCheckActions()
    {
      var actionDecls = program.Procedures.OfType<ActionDecl>().ToHashSet();
      var callGraph = new Graph<Procedure>();
      foreach (var actionDecl in actionDecls)
      {
        foreach (var block in actionDecl.Impl.Blocks)
        {
          foreach (var callCmd in block.Cmds.OfType<CallCmd>().Where(callCmd => !callCmd.IsAsync))
          {
            callGraph.AddEdge(actionDecl, callCmd.Proc);
          }
        }
      }
      if (!Graph<Procedure>.Acyclic(callGraph))
      {
        Error(program, "call graph over atomic actions must be acyclic");
      }
      actionDecls.Where(proc => proc.RefinedAction != null).ForEach(actionDecl =>
      {
        SignatureMatcher.CheckSequentializationSignature(actionDecl, actionDecl.RefinedAction.ActionDecl,
          checkingContext);
        if (actionDecl.InvariantAction != null)
        {
          SignatureMatcher.CheckSequentializationSignature(actionDecl, actionDecl.InvariantAction.ActionDecl,
            checkingContext);
        }
      });
      actionDecls.Where(x => x.RefinedAction != null && x.InvariantAction == null)
        .ForEach(x => TypeCheckInlineSequentializations(x));
      return actionDecls;
    }

    private void TypeCheckInlineSequentializations(ActionDecl actionDecl)
    {
      // compute eliminated actions and  check that there is no async call cycle among eliminated actions
      var refinedActionCreates = new HashSet<ActionDecl>(actionDecl.RefinedAction.ActionDecl.CreateActionDecls);
      var refinedActionCreateNames = refinedActionCreates.Select(x => x.Name).ToHashSet();
      var stack = new Stack<ActionDecl>();
      var frontier = new HashSet<ActionDecl>(); // hashset representation of stack for efficient membership check
      var visited = new HashSet<ActionDecl>();
      void Push(ActionDecl item)
      {
        stack.Push(item);
        frontier.Add(item);
      }
      void Pop(ActionDecl item)
      {
        stack.Pop();
        frontier.Remove(item);
      }

      Push(actionDecl);
      while (stack.Count != 0)
      {
        var item = stack.Peek();
        if (visited.Contains(item))
        {
          Pop(item);
          continue;
        }
        CheckAsyncToSyncSafety(item, refinedActionCreateNames);
        visited.Add(item);
        var hitOnStack = item.CreateActionDecls.FirstOrDefault(x => frontier.Contains(x));
        if (hitOnStack != null)
        {
          var callCycle = stack.TakeWhile(elem => elem != hitOnStack).Append(hitOnStack).Select(elem => elem.Name);
          Error(actionDecl, $"async call cycle detected: {string.Join(",", callCycle)}");
          break;
        }
        Pop(item);
        item.CreateActionDecls.Except(refinedActionCreates).ForEach(Push);
      }
    }

    private void CheckAsyncToSyncSafety(ActionDecl actionDecl, HashSet<string> refinedActionCreateNames)
    {
      actionDecl.Impl.Blocks.SelectMany(block => block.Cmds.OfType<CallCmd>().Where(callCmd =>
        callCmd.Proc.OriginalDeclWithFormals is { Name: "create_asyncs" or "create_multi_asyncs" })).ForEach(callCmd =>
      {
        var pendingAsyncType = (CtorType)program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
        if (!refinedActionCreateNames.Contains(pendingAsyncType.Decl.Name))
        {
          Error(callCmd, "unable to eliminate unbounded pending asyncs without invariant specification");
        }
      });

      var graph = Program.GraphFromImpl(actionDecl.Impl, false);
      var blocksLeadingToModifiedGlobals = new HashSet<Block>();
      graph.TopologicalSort().ForEach(block =>
      {
        var modifiedGlobals = block.TransferCmd is GotoCmd gotoCmd &&
                              gotoCmd.labelTargets.Any(x => blocksLeadingToModifiedGlobals.Contains(x));
        for (int i = block.Cmds.Count - 1; 0 <= i; i--)
        {
          var cmd = block.Cmds[i];
          if (modifiedGlobals && cmd is CallCmd callCmd && callCmd.IsAsync)
          {
            var pendingAsyncType = (CtorType)program.monomorphizer.GetTypeInstantiation(callCmd.Proc)["T"];
            if (!refinedActionCreateNames.Contains(pendingAsyncType.Decl.Name))
            {
              Error(callCmd, "unable to eliminate pending async since a global is modified subsequently");
            }
          }
          var assignedVariables = new List<Variable>();
          cmd.AddAssignedVariables(assignedVariables);
          if (assignedVariables.OfType<GlobalVariable>().Any())
          {
            modifiedGlobals = true;
          }
        }
        if (modifiedGlobals)
        {
          blocksLeadingToModifiedGlobals.Add(block);
        }
      });
    }

    private void TypeCheckYieldingProcedures()
    {
      foreach (var yieldingProc in program.Procedures.OfType<YieldProcedureDecl>())
      {
        foreach (var (header, yieldingLoop) in yieldingProc.YieldingLoops)
        {
          var availableLinearVarsAtHeader = new HashSet<Variable>(linearTypeChecker.AvailableLinearVars(header));
          yieldingLoop.YieldInvariants.ForEach(callCmd => linearTypeChecker.CheckLinearParameters(callCmd, availableLinearVarsAtHeader));
        }
        if (yieldingProc.RefinedAction != null)
        {
          SignatureMatcher.CheckRefinementSignature(yieldingProc, checkingContext);
        }
      }
      
      // local collectors for pending asyncs
      var pendingAsyncProcs = program.TopLevelDeclarations.OfType<ActionDecl>()
        .Where(proc => proc.MaybePendingAsync).Select(proc => proc.Name).ToHashSet();
      var pendingAsyncMultisetTypes = program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>()
        .Where(decl => pendingAsyncProcs.Contains(decl.Name)).Select(decl =>
          TypeHelper.MapType(TypeHelper.CtorType(decl), Type.Int)).ToHashSet();
      foreach (Implementation impl in program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var proc = (YieldProcedureDecl)impl.Proc;
        implToPendingAsyncCollectors[impl] = new Dictionary<CtorType, Variable>();
        foreach (Variable v in impl.LocVars.Where(v => v.HasAttribute(CivlAttributes.PENDING_ASYNC)))
        {
          if (!pendingAsyncMultisetTypes.Contains(v.TypedIdent.Type))
          {
            Error(v, "pending async collector is of incorrect type");
          }
          else if (v.LayerRange.LowerLayer != proc.Layer)
          {
            Error(v, "pending async collector must be introduced at the layer of the enclosing procedure");
          }
          else
          {
            var mapType = (MapType)v.TypedIdent.Type;
            var ctorType = (CtorType)mapType.Arguments[0];
            if (implToPendingAsyncCollectors[impl].ContainsKey(ctorType))
            {
              Error(v, "duplicate pending async collector");
            }
            else
            {
              implToPendingAsyncCollectors[impl][ctorType] = v;
            }
          }
        }
      }
    }
    
    private void InlineAtomicActions(HashSet<ActionDecl> actionDecls)
    {
      var primitiveImpls = program.TopLevelDeclarations.OfType<Implementation>().Where(impl =>
      {
        var originalDecl = impl.Proc.OriginalDeclWithFormals;
        return originalDecl != null && CivlPrimitives.LinearPrimitives.Contains(originalDecl.Name);
      });
      primitiveImpls.ForEach(impl => {
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      CivlUtil.AddInlineAttribute(SkipActionDecl);
      actionDecls.ForEach(proc =>
      {
        CivlAttributes.RemoveAttributes(proc, new HashSet<string> { "inline" });
        CivlUtil.AddInlineAttribute(proc);
      });
      actionDecls.ForEach(proc =>
      {
        var impl = proc.Impl;
        impl.OriginalBlocks = impl.Blocks;
        impl.OriginalLocVars = impl.LocVars;
      });
      actionDecls.ForEach(proc =>
      {
        Inliner.ProcessImplementation(Options, program, proc.Impl);
      });
      actionDecls.ForEach(proc =>
      {
        var impl = proc.Impl;
        impl.OriginalBlocks = null;
        impl.OriginalLocVars = null;
      });
      primitiveImpls.ForEach(impl => {
        impl.OriginalBlocks = null;
        impl.OriginalLocVars = null;
      });
    }

    private void CreateAtomicActions(HashSet<ActionDecl> actionDecls)
    {
      var invariantActionDecls = actionDecls.Where(decl => decl.InvariantAction != null)
        .Select(decl => decl.InvariantAction.ActionDecl).ToHashSet();

      // Initialize ActionDecls so that all the pending async machinery is set up.
      actionDecls.ForEach(proc => proc.Initialize(program.monomorphizer));

      // Create all actions that do not refine another action.
      foreach (var actionDecl in actionDecls.Where(proc => proc.RefinedAction == null))
      {
        actionDeclToAction[actionDecl] = new Action(this, actionDecl, null, invariantActionDecls.Contains(actionDecl));
      }
      
      // Create all atomic actions that refine other actions.
      actionDecls.Where(proc => proc.RefinedAction != null)
        .ForEach(decl => CreateActionsThatRefineAnotherAction(decl, invariantActionDecls));
    }
    
    private void CreateActionsThatRefineAnotherAction(ActionDecl actionDecl, HashSet<ActionDecl> invariantActionDecls)
    {
      if (actionDeclToAction.ContainsKey(actionDecl))
      {
        return;
      }
      var refinedProc = actionDecl.RefinedAction.ActionDecl;
      CreateActionsThatRefineAnotherAction(refinedProc, invariantActionDecls);
      var refinedAction = actionDeclToAction[refinedProc];
      actionDeclToAction[actionDecl] =
        new Action(this, actionDecl, refinedAction, invariantActionDecls.Contains(actionDecl));
    }

    private void CreateSequentializations(HashSet<ActionDecl> actionDecls)
    {
      actionDecls.Where(actionDecl => actionDecl.RefinedAction != null).ForEach(actionDecl =>
      {
        var action = actionDeclToAction[actionDecl];
        if (actionDecl.InvariantAction == null)
        {
          sequentializations.Add(new InlineSequentialization(this, action));
        }
        else
        {
          var invariantActionDecl = actionDecl.InvariantAction.ActionDecl;
          sequentializations.Add(new InductiveSequentialization(this, action, actionDeclToAction[invariantActionDecl]));
        }
      });
    }

    private class SignatureMatcher
    {
      public static void CheckRefinementSignature(YieldProcedureDecl proc, CheckingContext checkingContext)
      {
        var refinedActionDecl = proc.RefinedAction.ActionDecl;
        var signatureMatcher = new SignatureMatcher(proc, refinedActionDecl, checkingContext);
        var procInParams = proc.InParams.Where(x => proc.VisibleFormals.Contains(x)).ToList();
        var procOutParams = proc.OutParams.Where(x => proc.VisibleFormals.Contains(x)).ToList();
        var actionInParams = refinedActionDecl.InParams;
        var actionOutParams = refinedActionDecl.OutParams;
        signatureMatcher.MatchFormals(procInParams, actionInParams, SignatureMatcher.IN);
        signatureMatcher.MatchFormals(procOutParams, actionOutParams, SignatureMatcher.OUT);
      }

      public static void CheckSequentializationSignature(Procedure original, Procedure abstraction, CheckingContext checkingContext)
      {
        // Input and output parameters have to match exactly
        var signatureMatcher = new SignatureMatcher(original, abstraction, checkingContext);
        signatureMatcher.MatchFormals(original.InParams, abstraction.InParams, SignatureMatcher.IN);
        signatureMatcher.MatchFormals(original.OutParams, abstraction.OutParams, SignatureMatcher.OUT);
      }

      private static string IN = "in";
      private static string OUT = "out";
      private DeclWithFormals decl1;
      private DeclWithFormals decl2;
      private CheckingContext checkingContext;

      private SignatureMatcher(DeclWithFormals decl1, DeclWithFormals decl2, CheckingContext checkingContext)
      {
        this.decl1 = decl1;
        this.decl2 = decl2;
        this.checkingContext = checkingContext;
      }

      private void MatchFormals(List<Variable> formals1, List<Variable> formals2, string inout, bool checkLinearity = true)
      {
        if (formals1.Count != formals2.Count)
        {
          checkingContext.Error(decl1, $"mismatched number of {inout}-parameters in {decl2.Name}");
        }
        else
        {
          for (int i = 0; i < formals1.Count; i++)
          {
            // For error messages below
            string name1 = formals1[i].Name;
            string name2 = formals2[i].Name;
            
            Type t1 = formals1[i].TypedIdent.Type;
            Type t2 = formals2[i].TypedIdent.Type;
            if (name1 != name2)
            {
              checkingContext.Error(formals1[i], $"mismatched name of {inout}-parameter {name1}: (named {name2} in {decl2.Name})");
            }
            else if (!t1.Equals(t2))
            {
              checkingContext.Error(formals1[i], $"mismatched type of {inout}-parameter {name1} in {decl2.Name}");
            }
            else if (checkLinearity &&
                (QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR) !=
                 QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR) ||
                 QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_IN) !=
                 QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_IN) ||
                 QKeyValue.FindStringAttribute(formals1[i].Attributes, CivlAttributes.LINEAR_OUT) !=
                 QKeyValue.FindStringAttribute(formals2[i].Attributes, CivlAttributes.LINEAR_OUT)))
            {
              checkingContext.Error(formals1[i],
                $"mismatched linearity annotation of {inout}-parameter {name1} in {decl2.Name}");
            }
          }
        }
      }
    }
    
    #region Public access methods

    public IEnumerable<Variable> GlobalVariables => program.GlobalVariables;

    public IEnumerable<Variable> GlobalVariablesAtLayer(int layerNum)
    {
      return GlobalVariables.Where(v => v.LayerRange.LowerLayer <= layerNum && layerNum < v.LayerRange.UpperLayer);
    }

    public IEnumerable<Action> MoverActions => actionDeclToAction.Keys
      .Where(actionDecl => actionDecl.HasMoverType).Select(actionDecl => actionDeclToAction[actionDecl]);

    public IEnumerable<Action> AtomicActions => actionDeclToAction.Values;

    public Action Action(ActionDecl actionDecl)
    {
      return actionDeclToAction[actionDecl];
    }
    
    public IEnumerable<Sequentialization> Sequentializations => sequentializations;

    public Dictionary<CtorType, Variable> PendingAsyncCollectors(Implementation impl)
    {
      return implToPendingAsyncCollectors[impl];
    }

    public void Error(Absy node, string message)
    {
      checkingContext.Error(node, message);
    }

    #endregion

    private class VariableNameCollector : ReadOnlyVisitor
    {
      private HashSet<string> localVarNames = new HashSet<string>();

      public static HashSet<string> Collect(Program program)
      {
        var collector = new VariableNameCollector();
        collector.VisitProgram(program);
        return collector.localVarNames;
      }

      public override Variable VisitVariable(Variable node)
      {
        localVarNames.Add(node.Name);
        return node;
      }
    }
    
    private class AttributeEraser : ReadOnlyVisitor
    {
      public static void Erase(CivlTypeChecker civlTypeChecker)
      {
        var attributeEraser = new AttributeEraser();
        attributeEraser.VisitProgram(civlTypeChecker.program);
        foreach (var action in civlTypeChecker.AtomicActions)
        {
          attributeEraser.VisitAtomicAction(action);
        }
      }

      public override Procedure VisitProcedure(Procedure node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitProcedure(node);
      }

      public override Implementation VisitImplementation(Implementation node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitImplementation(node);
      }

      public override Requires VisitRequires(Requires node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitRequires(node);
      }

      public override Ensures VisitEnsures(Ensures node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitEnsures(node);
      }

      public override Cmd VisitAssertCmd(AssertCmd node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitAssertCmd(node);
      }

      public override Variable VisitVariable(Variable node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitVariable(node);
      }

      public override Function VisitFunction(Function node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitFunction(node);
      }

      public override Declaration VisitDeclaration(Declaration node)
      {
        CivlAttributes.RemoveCivlAttributes(node);
        return base.VisitDeclaration(node);
      }

      public void VisitAtomicAction(Action action)
      {
        Visit(action.FirstImpl);
        Visit(action.SecondImpl);
      }
    }
  }
}
