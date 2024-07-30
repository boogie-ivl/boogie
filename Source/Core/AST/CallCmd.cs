using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class CallCmd : CallCommonality
{
  public string /*!*/ callee { get; set; }
  public Procedure Proc;
  public LocalVariable AssignedAssumptionVariable;

  // Element of the following lists can be null, which means that
  // the call happens with * as these parameters
  public List<Expr> /*!*/
    Ins;

  public List<IdentifierExpr> /*!*/
    Outs;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(callee != null);
    Contract.Invariant(Ins != null);
    Contract.Invariant(Outs != null);
  }

  //public Lattice.Element StateAfterCall;

  // The instantiation of type parameters that is determined during
  // type checking
  public TypeParamInstantiation TypeParameters = null;

  public ProofObligationDescription Description { get; set; } = new PreconditionDescription();

  public CallCmd(IToken tok, string callee, List<Expr> ins, List<IdentifierExpr> outs)
    : base(tok, null)
  {
    Contract.Requires(outs != null);
    Contract.Requires(ins != null);
    Contract.Requires(callee != null);
    Contract.Requires(tok != null);
    this.callee = callee;
    this.Ins = ins;
    this.Outs = outs;
  }

  public CallCmd(IToken tok, string callee, List<Expr> ins, List<IdentifierExpr> outs, QKeyValue kv)
    : base(tok, kv)
  {
    Contract.Requires(outs != null);
    Contract.Requires(ins != null);
    Contract.Requires(callee != null);
    Contract.Requires(tok != null);
    this.callee = callee;
    this.Ins = ins;
    this.Outs = outs;
  }

  public CallCmd(IToken tok, string callee, List<Expr> ins, List<IdentifierExpr> outs, QKeyValue kv, bool IsAsync)
    : base(tok, kv)
  {
    Contract.Requires(outs != null);
    Contract.Requires(ins != null);
    Contract.Requires(callee != null);
    Contract.Requires(tok != null);
    this.callee = callee;
    this.Ins = ins;
    this.Outs = outs;
    this.IsAsync = IsAsync;
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    stream.Write(this, level, "");
    if (IsFree)
    {
      stream.Write("free ");
    }

    if (IsAsync)
    {
      stream.Write("async ");
    }

    stream.Write("call ");
    EmitAttributes(stream, Attributes);
    string sep = "";
    if (Outs.Count > 0)
    {
      foreach (Expr arg in Outs)
      {
        stream.Write(sep);
        sep = ", ";
        if (arg == null)
        {
          stream.Write("*");
        }
        else
        {
          arg.Emit(stream);
        }
      }

      stream.Write(" := ");
    }

    stream.Write(TokenTextWriter.SanitizeIdentifier(callee));
    stream.Write("(");
    sep = "";
    foreach (Expr arg in Ins)
    {
      stream.Write(sep);
      sep = ", ";
      if (arg == null)
      {
        stream.Write("*");
      }
      else
      {
        arg.Emit(stream);
      }
    }

    stream.WriteLine(");");
    base.Emit(stream, level);
  }

  public override void Resolve(ResolutionContext rc)
  {
    if (Proc != null)
    {
      // already resolved
      return;
    }

    (this as ICarriesAttributes).ResolveAttributes(rc);
    Proc = rc.LookUpProcedure(callee);
    if (Proc == null)
    {
      rc.Error(this, "call to undeclared procedure: {0}", callee);
    }

    foreach (Expr e in Ins)
    {
      if (e != null)
      {
        e.Resolve(rc);
      }
    }

    HashSet<Variable> actualOuts = new HashSet<Variable>();
    foreach (IdentifierExpr ide in Outs)
    {
      if (ide != null)
      {
        ide.Resolve(rc);
        if (ide.Decl != null)
        {
          if (actualOuts.Contains(ide.Decl))
          {
            rc.Error(this, "left-hand side of call command contains variable twice: {0}", ide.Name);
          }
          else
          {
            actualOuts.Add(ide.Decl);
          }
        }
      }
    }

    if (Proc == null)
    {
      return;
    }

    // first make sure that the right number of parameters is given
    // (a similar check is in CheckArgumentTypes, but we are not
    // able to call this method because it cannot cope with Ins/Outs
    // that are null)
    if (Ins.Count != Proc.InParams.Count)
    {
      rc.Error(this.tok,
        "wrong number of arguments in call to {0}: {1}",
        callee, Ins.Count);
      return;
    }

    if (Outs.Count != Proc.OutParams.Count)
    {
      rc.Error(this.tok,
        "wrong number of result variables in call to {0}: {1}",
        callee, Outs.Count);
      return;
    }

    if (IsAsync)
    {
      if (Proc.OutParams.Count > 0)
      {
        rc.Error(this.tok, "a procedure called asynchronously cannot have output parameters");
        return;
      }
    }

    (this as ICarriesAttributes).ResolveAttributes(rc);
    Layers = (this as ICarriesAttributes).FindLayers();
    if (rc.Proc is YieldProcedureDecl callerDecl) {
      if (Layers.Count > 2)
      {
        rc.Error(this, "expected layer range");
      }
      else if (Layers.Count == 0)
      {
        Layers = new List<int>{ LayerRange.Min, callerDecl.Layer };
      }
      else if (Layers[^1] > callerDecl.Layer)
      {
        rc.Error(this, $"layer must be no more than layer {callerDecl.Layer}");
      }
    }

    var id = QKeyValue.FindStringAttribute(Attributes, "id");
    if (id != null)
    {
      rc.AddStatementId(tok, id);
    }
      
    if (rc.Proc.GetType() == typeof(Procedure))
    {
      if (Proc.GetType() != typeof(Procedure))
      {
        rc.Error(this, "a procedure may only call other procedures");
      }
    }
    if (rc.Proc.IsPure && !Proc.IsPure)
    {
      rc.Error(this, "pure procedure may only call a pure procedure");
    }
    if (rc.Proc is YieldProcedureDecl)
    {
      if (Proc.IsPure || Proc is YieldProcedureDecl or YieldInvariantDecl)
      {
        // call ok
      }
      else
      {
        rc.Error(this,
          "a yielding procedure may only call pure actions, pure procedures, yield procedures, and yield invariants");
      }
    }
    if (IsAsync)
    {
      if (rc.Proc is ActionDecl)
      {
        if (Proc is not ActionDecl)
        {
          rc.Error(this, "target of async call must be an action");
        }
      }
      else if (rc.Proc is YieldProcedureDecl)
      {
        if (Proc is not YieldProcedureDecl)
        {
          rc.Error(this, "target of async call must be a yield procedure");
        }
      }
      else
      {
        rc.Error(this, "async call allowed only from a yield procedure or an action");
      }
    }
    // checking calls from atomic actions need type information, hence postponed to type checking
  }

  private void TypecheckCallCmdInYieldProcedureDecl(TypecheckingContext tc)
  {
    if (tc.Proc is not YieldProcedureDecl callerDecl)
    {
      return;
    }

    var callerModifiedVars = new HashSet<Variable>(callerDecl.ModifiedVars);

    void CheckModifies(IEnumerable<Variable> modifiedVars)
    {
      if (!callerDecl.HasMoverType)
      {
        return;
      }
      foreach (var v in modifiedVars.Where(v => !callerModifiedVars.Contains(v)))
      {
        tc.Error(this, $"modified variable does not appear in modifies clause of mover procedure: {v.Name}");
      }
    }

    // check layers
    if (Proc is YieldProcedureDecl calleeDecl)
    {
      var isSynchronized = this.HasAttribute(CivlAttributes.SYNC);
      var isSkipped = this.HasAttribute(CivlAttributes.SKIP);
      if (calleeDecl.Layer > callerDecl.Layer)
      {
        tc.Error(this, "layer of callee must not be more than layer of caller");
      }
      else if (!calleeDecl.HasMoverType)
      {
        if (callerDecl.Layer > calleeDecl.Layer)
        {
          if (calleeDecl.RefinedAction != null)
          {
            var highestRefinedActionDecl = calleeDecl.RefinedActionAtLayer(callerDecl.Layer);
            if (highestRefinedActionDecl == null)
            {
              tc.Error(this, $"called action is not available at layer {callerDecl.Layer}");
            }
            else
            {
              CheckModifies(highestRefinedActionDecl.ModifiedVars);
              if (!IsAsync)
              {
                if (highestRefinedActionDecl.Creates.Any() && callerDecl.HasMoverType)
                {
                  tc.Error(this, "caller must not be a mover procedure");
                }
                // check there is no application of IS_RIGHT in the entire chain of refined actions
                var calleeRefinedAction = calleeDecl.RefinedAction;
                while (calleeRefinedAction != null)
                {
                  if (calleeRefinedAction.HasAttribute(CivlAttributes.IS_RIGHT))
                  {
                    tc.Error(this, "this must be an async call");
                    break;
                  }
                  var calleeActionDecl = calleeRefinedAction.ActionDecl;
                  if (calleeActionDecl == highestRefinedActionDecl)
                  {
                    break;
                  }
                  calleeRefinedAction = calleeActionDecl.RefinedAction;
                }
              }
              else if (isSynchronized)
              {
                // check that entire chain of refined actions all the way to highestRefinedAction is comprised of left movers
                var calleeRefinedAction = calleeDecl.RefinedAction;
                while (calleeRefinedAction != null)
                {
                  var calleeActionDecl = calleeRefinedAction.ActionDecl;
                  if (!calleeActionDecl.IsLeftMover)
                  {
                    tc.Error(this,
                      $"callee abstraction in synchronized call must be a left mover: {calleeActionDecl.Name}");
                    break;
                  }
                  if (calleeActionDecl == highestRefinedActionDecl)
                  {
                    break;
                  }
                  calleeRefinedAction = calleeActionDecl.RefinedAction;
                }
              }
              else if (isSkipped)
              {
                if (highestRefinedActionDecl.LayerRange.UpperLayer != callerDecl.Layer)
                {
                  tc.Error(this, $"upper layer of action {highestRefinedActionDecl.Name} must be same as layer of caller");
                }
                else if (!highestRefinedActionDecl.IsSkippable())
                {
                  tc.Error(this, $"action {highestRefinedActionDecl.Name} must be skippable");
                }
              }
            }
          }
        }
        else // callerDecl.Layer == calleeDecl.Layer
        {
          if (callerDecl.HasMoverType)
          {
            tc.Error(this, "caller must not be a mover procedure");
          }
          else if (IsAsync && calleeDecl.RefinedAction != null)
          {
            if (isSynchronized)
            {
              tc.Error(this, "layer of callee in synchronized call must be less than layer of caller");
            }
            else
            {
              var highestRefinedAction = calleeDecl.RefinedActionAtLayer(callerDecl.Layer + 1);
              if (highestRefinedAction == null)
              {
                tc.Error(this, $"called action is not available at layer {callerDecl.Layer + 1}");
              }
              else if (!highestRefinedAction.MaybePendingAsync)
              {
                tc.Error(this, $"action {highestRefinedAction.Name} refined by callee must be eligible to be a pending async");
              }
            }
          }
        }
      }
      else // calleeDecl.HasMoverType
      {
        if (callerDecl.Layer > calleeDecl.Layer)
        {
          tc.Error(this, "layer of caller must be equal to layer of callee");
        }
        else
        {
          CheckModifies(calleeDecl.ModifiedVars);
          if (IsAsync)
          {
            if (!isSynchronized)
            {
              tc.Error(this, "async call to mover procedure must be synchronized");
            }
            else if (!calleeDecl.IsLeftMover)
            {
              tc.Error(this, "callee in synchronized call must be a left mover");
            }
          }
        }
      }
    }
    else if (Proc is YieldInvariantDecl yieldInvariantDecl)
    {
      if (yieldInvariantDecl.Layer > callerDecl.Layer)
      {
        tc.Error(this, "layer of callee must not be more than layer of caller");
      }
    }
    else
    {
      Debug.Assert(Proc.IsPure);
      var usedVars = VariableCollector.Collect(Ins.Union(Outs));
      if (usedVars.OfType<GlobalVariable>().Any())
      {
        if (Layers.Count == 2)
        {
          tc.Error(this, "expected singleton layer range");
        }
        else
        {
          // Check global outputs only; the checking of local outputs is done later
          var calleeLayer = Layers[0];
          var globalOutputs = Outs.Select(ie => ie.Decl).OfType<GlobalVariable>().Cast<Variable>();
          if (CivlPrimitives.LinearPrimitives.Contains(Proc.Name))
          {
            var modifiedArgument = CivlPrimitives.ModifiedArgument(this);
            if (modifiedArgument is { Decl: GlobalVariable })
            {
              globalOutputs = globalOutputs.Append(modifiedArgument.Decl);
            }
          }
          globalOutputs.Where(v => v.LayerRange.LowerLayer != calleeLayer).ForEach(v =>
          {
            tc.Error(this, $"variable must be introduced at layer {calleeLayer}: {v.Name}");
          });
          if (calleeLayer < callerDecl.Layer)
          {
            globalOutputs.Where(v => v.LayerRange.UpperLayer != calleeLayer).ForEach(v =>
            {
              tc.Error(this, $"variable must be hidden at layer {calleeLayer}: {v.Name}");
            });
          }
        }
      }
    }
  }

  private void TypecheckCallCmdInActionDecl(TypecheckingContext tc)
  {
    if (tc.Proc is not ActionDecl callerActionDecl)
    {
      return;
    }

    if (CivlPrimitives.LinearPrimitives.Contains(Proc.Name))
    {
      // ok
    }
    else if (Proc.OriginalDeclWithFormals != null && CivlPrimitives.Async.Contains(Proc.OriginalDeclWithFormals.Name))
    {
      // ok
    }
    else if (IsAsync)
    {
      if (callerActionDecl.Creates.All(x => x.ActionName != Proc.Name))
      {
        tc.Error(this, "pending async must be in the creates clause of caller");
      }
    }
    else if (CivlPrimitives.Async.Contains(Proc.Name))
    {
      var type = TypeProxy.FollowProxy(TypeParameters[Proc.TypeParameters[0]].Expanded);
      if (type is CtorType { Decl: DatatypeTypeCtorDecl datatypeTypeCtorDecl })
      {
        if (callerActionDecl.Creates.All(x => x.ActionName != datatypeTypeCtorDecl.Name))
        {
          tc.Error(this, "primitive call must be instantiated with a pending async type in the creates clause of caller");
        }
      }
      else
      {
        tc.Error(this, "primitive call must be instantiated with a pending async type");
      }
    }
    else if (Proc is ActionDecl calleeActionDecl)
    {
      foreach (var actionDeclRef in calleeActionDecl.Creates)
      {
        if (callerActionDecl.Creates.All(x => x.ActionDecl != actionDeclRef.ActionDecl))
        {
          tc.Error(actionDeclRef, "callee creates a pending async not in the creates clause of caller");
        }
      }
      if (!callerActionDecl.LayerRange.Subset(calleeActionDecl.LayerRange))
      {
        tc.Error(this,
          $"caller layer range ({callerActionDecl.LayerRange}) must be subset of callee layer range ({calleeActionDecl.LayerRange})");
      }
    }
    else if (tc.Impl == null)
    {
      // call to yield invariant allowed only in preconditions
      var yieldInvariantDecl = (YieldInvariantDecl)Proc;
      if (!callerActionDecl.LayerRange.Contains(yieldInvariantDecl.Layer))
      {
        tc.Error(this, "layer of callee must be in the layer range of caller");
      }
    }
    else
    {
      tc.Error(this, "an action may only call actions or primitives");
    }
  }

  public override void AddAssignedVariables(List<Variable> vars)
  {
    if (this.IsAsync)
    {
      return;
    }

    foreach (IdentifierExpr e in Outs)
    {
      if (e != null)
      {
        vars.Add(e.Decl);
      }
    }

    Contract.Assume(this.Proc != null);
    foreach (IdentifierExpr /*!*/ e in this.Proc.Modifies)
    {
      Contract.Assert(e != null);
      vars.Add(e.Decl);
    }

    if (AssignedAssumptionVariable != null)
    {
      vars.Add(AssignedAssumptionVariable);
    }
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    Contract.Assume(this.Proc !=
                    null); // we assume the CallCmd has been successfully resolved before calling this Typecheck method

    var errorCount = tc.ErrorCount;

    (this as ICarriesAttributes).TypecheckAttributes(tc);

    List<LayerRange> expectedLayerRanges = null;
    if (tc.Proc is YieldProcedureDecl callerDecl)
    {
      for (int i = 0; i < Proc.OutParams.Count; i++)
      {
        var formal = Proc.OutParams[i];
        var actual = Outs[i];
        if (actual.Decl is GlobalVariable)
        {
          if (!Proc.IsPure) // global outputs of pure calls already checked
          {
            tc.Error(actual, $"global variable directly modified in a yield procedure: {actual.Decl.Name}");
          }
        }
        else
        {
          var formalLayerRange = FormalLayerRange(callerDecl, formal);
          if (!actual.Decl.LayerRange.Subset(formalLayerRange))
          {
            tc.Error(this, $"variable must be available only within layers in {formalLayerRange}: {actual.Decl.Name}");
          }
        }
      }
      // primitive calls have inout parameters that must be checked here
      if (CivlPrimitives.LinearPrimitives.Contains(Proc.Name))
      {
        var modifiedArgument = CivlPrimitives.ModifiedArgument(this);
        if (modifiedArgument == null)
        {
          // nothing to do
        }
        else if (modifiedArgument is { Decl: GlobalVariable })
        {
          // already done in TypecheckCallCmdInYieldProcedureDecl
        }
        else
        {
          var modifiedDecl = modifiedArgument.Decl;
          var callLayerRange = new LayerRange(Layers[0], Layers.Count > 1 ? Layers[1] : Layers[0]);
          if (!modifiedDecl.LayerRange.Subset(callLayerRange))
          {
            tc.Error(this, $"variable must be available only within layers in {callLayerRange}: {modifiedDecl.Name}");
          }
        }
      }
      expectedLayerRanges = Proc.InParams.Select(formal => FormalLayerRange(callerDecl, formal)).ToList();
    }

    // typecheck in-parameters
    for (int i = 0; i < Ins.Count; i++)
    {
      var e = Ins[i];
      if (e != null)
      {
        tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl && Proc is YieldProcedureDecl;
        tc.ExpectedLayerRange = expectedLayerRanges?[i];
        e.Typecheck(tc);
        tc.GlobalAccessOnlyInOld = false;
        tc.ExpectedLayerRange = null;
      }
    }

    for (int i = 0; i < Outs.Count; i++)
    {
      var e = Outs[i];
      if (e != null)
      {
        e.Typecheck(tc);
      }
    }

    this.CheckAssignments(tc);

    List<Type> /*!*/
      formalInTypes = new List<Type>();
    List<Type> /*!*/
      formalOutTypes = new List<Type>();
    List<Expr> /*!*/
      actualIns = new List<Expr>();
    List<IdentifierExpr> /*!*/
      actualOuts = new List<IdentifierExpr>();
    for (int i = 0; i < Ins.Count; ++i)
    {
      if (Ins[i] != null)
      {
        formalInTypes.Add(cce.NonNull(Proc.InParams[i]).TypedIdent.Type);
        actualIns.Add(Ins[i]);
      }
    }

    for (int i = 0; i < Outs.Count; ++i)
    {
      if (Outs[i] != null)
      {
        formalOutTypes.Add(cce.NonNull(Proc.OutParams[i]).TypedIdent.Type);
        actualOuts.Add(Outs[i]);
      }
    }

    // match actuals with formals
    Type.CheckArgumentTypes(Proc.TypeParameters,
      out var actualTypeParams,
      formalInTypes, actualIns,
      formalOutTypes, actualOuts,
      this.tok,
      "call to " + callee,
      tc);
    Contract.Assert(cce.NonNullElements(actualTypeParams));
    TypeParameters = SimpleTypeParamInstantiation.From(Proc.TypeParameters,
      actualTypeParams);

    if (tc.ErrorCount > errorCount)
    {
      return;
    }
    TypecheckCallCmdInYieldProcedureDecl(tc);
    TypecheckCallCmdInActionDecl(tc);
  }

  public LayerRange LayerRange => Layers.Count == 0 ? LayerRange.MinMax :
    Layers.Count == 1 ? new LayerRange(Layers[0]) : new LayerRange(Layers[0], Layers[1]);

  private LayerRange FormalLayerRange(YieldProcedureDecl callerDecl, Variable calleeFormal)
  {
    LayerRange formalLayerRange;
    switch (Proc)
    {
      case YieldInvariantDecl yieldInvariantDecl:
        formalLayerRange = new LayerRange(yieldInvariantDecl.Layer);
        break;
      case YieldProcedureDecl yieldProcedureDecl:
      {
        formalLayerRange = calleeFormal.LayerRange;
        if (!yieldProcedureDecl.HasMoverType && yieldProcedureDecl.VisibleFormals.Contains(calleeFormal))
        {
          formalLayerRange = new LayerRange(formalLayerRange.LowerLayer, callerDecl.Layer);
        }
        break;
      }
      default:
      {
        Debug.Assert(Proc.IsPure);
        formalLayerRange = LayerRange;
        break;
      }
    }
    return formalLayerRange;
  }

  private IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ TypeParamSubstitution()
  {
    Contract.Ensures(cce.NonNullDictionaryAndValues(Contract.Result<IDictionary<TypeVariable, Type>>()));
    Contract.Assume(TypeParameters != null);
    IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
      res = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
    foreach (TypeVariable /*!*/ v in TypeParameters.FormalTypeParams)
    {
      Contract.Assert(v != null);
      res.Add(v, TypeParameters[v]);
    }

    return res;
  }

  protected override Cmd ComputeDesugaring(PrintOptions options)
  {
    Contract.Ensures(Contract.Result<Cmd>() != null);

    int uniqueId = 0;
    List<Cmd> newBlockBody = new List<Cmd>();
    Dictionary<Variable, Expr> substMap = new Dictionary<Variable, Expr>();
    Dictionary<Variable, Expr> substMapOld = new Dictionary<Variable, Expr>();
    Dictionary<Variable, Expr> substMapBound = new Dictionary<Variable, Expr>();
    List<Variable> /*!*/
      tempVars = new List<Variable>();
    string callId = (this as ICarriesAttributes).FindStringAttribute("id");

    // proc P(ins) returns (outs)
    //   requires Pre
    //   //modifies frame
    //   ensures Post
    //
    // call aouts := P(ains)

    // ins    : formal in parameters of procedure
    // frame  : a list of global variables from the modifies clause
    // outs   : formal out parameters of procedure
    // ains   : actual in arguments passed to call
    // aouts  : actual variables assigned to from call
    // cins   : new variables created just for this call, one per ains
    // cframe : new variables created just for this call, to keep track of OLD values
    // couts  : new variables created just for this call, one per aouts
    // WildcardVars : new variables created just for this call, one per null in ains

    #region Create cins; each one is an incarnation of the corresponding in parameter

    List<Variable> /*!*/
      cins = new List<Variable>();
    List<Variable> wildcardVars = new List<Variable>();
    Contract.Assume(this.Proc != null);
    for (int i = 0; i < this.Proc.InParams.Count; ++i)
    {
      Variable /*!*/
        param = cce.NonNull(this.Proc.InParams[i]);
      bool isWildcard = this.Ins[i] == null;

      Type /*!*/
        actualType;
      if (isWildcard)
      {
        actualType = param.TypedIdent.Type.Substitute(TypeParamSubstitution());
      }
      else
      {
        // during type checking, we have ensured that the type of the actual
        // parameter Ins[i] is correct, so we can use it here
        actualType = cce.NonNull(cce.NonNull(Ins[i]).Type);
      }

      Variable cin = CreateTemporaryVariable(tempVars, param, actualType,
        TempVarKind.Formal, ref uniqueId);
      cins.Add(cin);
      IdentifierExpr ie = new IdentifierExpr(cin.tok, cin);
      substMap.Add(param, ie);
      if (isWildcard)
      {
        cin = CreateTemporaryVariable(tempVars, param,
          actualType, TempVarKind.Bound, ref uniqueId);
        wildcardVars.Add(cin);
        ie = new IdentifierExpr(cin.tok, cin);
      }

      substMapBound.Add(param, ie);
    }

    #endregion

    #region call aouts := P(ains) becomes: (open outlining one level to see)

    #region cins := ains (or havoc cin when ain is null)

    for (int i = 0, n = this.Ins.Count; i < n; i++)
    {
      IdentifierExpr /*!*/
        cin_exp = new IdentifierExpr(cce.NonNull(cins[i]).tok, cce.NonNull(cins[i]));
      Contract.Assert(cin_exp != null);
      if (this.Ins[i] != null)
      {
        AssignCmd assign = Cmd.SimpleAssign(Token.NoToken, cin_exp, cce.NonNull(this.Ins[i]));
        newBlockBody.Add(assign);
      }
      else
      {
        List<IdentifierExpr> /*!*/
          ies = new List<IdentifierExpr>();
        ies.Add(cin_exp);
        HavocCmd havoc = new HavocCmd(Token.NoToken, ies);
        newBlockBody.Add(havoc);
      }
    }

    #endregion

    #region assert (exists wildcardVars :: Pre[ins := cins])

    Substitution s = Substituter.SubstitutionFromDictionary(substMapBound);
    bool hasWildcard = (wildcardVars.Count != 0);
    Expr preConjunction = null;
    for (int i = 0; i < this.Proc.Requires.Count; i++)
    {
      Requires /*!*/
        req = cce.NonNull(this.Proc.Requires[i]);
      if (!req.Free && !IsFree)
      {
        if (hasWildcard)
        {
          Expr pre = Substituter.Apply(s, req.Condition);
          if (preConjunction == null)
          {
            preConjunction = pre;
          }
          else
          {
            preConjunction = Expr.And(preConjunction, pre);
          }
        }
        else
        {
          Requires /*!*/
            reqCopy = (Requires /*!*/) cce.NonNull(req.Clone());
          reqCopy.Condition = Substituter.Apply(s, req.Condition);
          AssertCmd /*!*/
            a = new AssertRequiresCmd(this, reqCopy);
          Contract.Assert(a != null);

          if (Attributes != null)
          {
            // Inherit attributes of call.
            var attrCopy = (QKeyValue) cce.NonNull(Attributes.Clone());
            attrCopy = Substituter.Apply(s, attrCopy);
            a.Attributes = attrCopy;
          }

          // Do this after copying the attributes so it doesn't get overwritten
          if (callId is not null) {
            (a as ICarriesAttributes).CopyIdWithModificationsFrom(tok, req,
              id => new TrackedCallRequiresGoal(callId, id));
          }

          a.ErrorDataEnhanced = reqCopy.ErrorDataEnhanced;
          newBlockBody.Add(a);
        }
      }
      else if (req.CanAlwaysAssume()
               || options.StratifiedInlining > 0)
      {
        // inject free requires as assume statements at the call site
        AssumeCmd /*!*/
          a = new AssumeCmd(req.tok, Substituter.Apply(s, req.Condition));
        Contract.Assert(a != null);
        // These probably won't have IDs, but copy if they do.
        if (callId is not null) {
          (a as ICarriesAttributes).CopyIdWithModificationsFrom(tok, req,
            id => new TrackedCallRequiresAssumed(callId, id));
        }

        newBlockBody.Add(a);
      }
    }

    if (hasWildcard)
    {
      if (preConjunction == null)
      {
        preConjunction = Expr.True;
      }

      Expr /*!*/
        expr = new ExistsExpr(tok, wildcardVars, preConjunction);
      Contract.Assert(expr != null);
      AssertCmd /*!*/
        a = new AssertCmd(tok, expr);
      Contract.Assert(a != null);
      if (Attributes != null)
      {
        // Inherit attributes of call.
        var attrCopy = (QKeyValue) cce.NonNull(Attributes.Clone());
        attrCopy = Substituter.Apply(s, attrCopy);
        a.Attributes = attrCopy;
      }

      a.ErrorDataEnhanced = AssertCmd.GenerateBoundVarMiningStrategy(expr);
      newBlockBody.Add(a);
    }

    #endregion

    #region assume Pre[ins := cins] with formal paramters

    if (hasWildcard)
    {
      s = Substituter.SubstitutionFromDictionary(substMap);
      for (int i = 0; i < this.Proc.Requires.Count; i++)
      {
        Requires /*!*/
          req = cce.NonNull(this.Proc.Requires[i]);
        if (!req.Free)
        {
          Requires /*!*/
            reqCopy = (Requires /*!*/) cce.NonNull(req.Clone());
          reqCopy.Condition = Substituter.Apply(s, req.Condition);
          AssumeCmd /*!*/
            a = new AssumeCmd(tok, reqCopy.Condition);
          Contract.Assert(a != null);
          newBlockBody.Add(a);
        }
      }
    }

    #endregion

    #region cframe := frame (to hold onto frame values in case they are referred to in the postcondition)

    List<IdentifierExpr> havocVarExprs = new List<IdentifierExpr>();

    foreach (IdentifierExpr /*!*/ f in this.Proc.Modifies)
    {
      Contract.Assert(f != null);
      Contract.Assume(f.Decl != null);
      Contract.Assert(f.Type != null);
      Variable v = CreateTemporaryVariable(tempVars, f.Decl, f.Type, TempVarKind.Old, ref uniqueId);
      IdentifierExpr v_exp = new IdentifierExpr(v.tok, v);
      substMapOld.Add(f.Decl, v_exp); // this assumes no duplicates in this.Proc.Modifies
      AssignCmd assign = Cmd.SimpleAssign(f.tok, v_exp, f);
      newBlockBody.Add(assign);

      // fra
      if (!havocVarExprs.Contains(f))
      {
        havocVarExprs.Add(f);
      }
    }

    #endregion

    #region Create couts

    List<Variable> /*!*/
      couts = new List<Variable>();
    for (int i = 0; i < this.Proc.OutParams.Count; ++i)
    {
      Variable /*!*/
        param = cce.NonNull(this.Proc.OutParams[i]);
      bool isWildcard = this.Outs[i] == null;

      Type /*!*/
        actualType;
      if (isWildcard)
      {
        actualType = param.TypedIdent.Type.Substitute(TypeParamSubstitution());
      }
      else
      {
        // during type checking, we have ensured that the type of the actual
        // out parameter Outs[i] is correct, so we can use it here
        actualType = cce.NonNull(cce.NonNull(Outs[i]).Type);
      }

      Variable cout = CreateTemporaryVariable(tempVars, param, actualType,
        TempVarKind.Formal, ref uniqueId);
      couts.Add(cout);
      IdentifierExpr ie = new IdentifierExpr(cout.tok, cout);
      substMap.Add(param, ie);

      if (!havocVarExprs.Contains(ie))
      {
        havocVarExprs.Add(ie);
      }
    }

    // add the where clauses, now that we have the entire substitution map
    foreach (Variable /*!*/ param in this.Proc.OutParams)
    {
      Contract.Assert(param != null);
      Expr w = param.TypedIdent.WhereExpr;
      if (w != null)
      {
        IdentifierExpr ie = (IdentifierExpr /*!*/) cce.NonNull(substMap[param]);
        Contract.Assert(ie.Decl != null);
        ie.Decl.TypedIdent.WhereExpr = Substituter.Apply(Substituter.SubstitutionFromDictionary(substMap), w);
      }
    }

    #endregion

    #region havoc frame, couts

    // pass on this's token
    HavocCmd hc = new HavocCmd(this.tok, havocVarExprs);
    newBlockBody.Add(hc);

    #endregion

    #region assume Post[ins, outs, old(frame) := cins, couts, cframe]

    calleeSubstitution = Substituter.SubstitutionFromDictionary(substMap, true, Proc);
    calleeSubstitutionOld = Substituter.SubstitutionFromDictionary(substMapOld, true, Proc);
    foreach (Ensures /*!*/ e in this.Proc.Ensures)
    {
      Contract.Assert(e != null);
      Expr copy = Substituter.ApplyReplacingOldExprs(calleeSubstitution, calleeSubstitutionOld, e.Condition);
      AssumeCmd assume = new AssumeCmd(this.tok, copy);

      #region stratified inlining support

      if (QKeyValue.FindBoolAttribute(e.Attributes, "si_fcall"))
      {
        assume.Attributes = Attributes;
      }

      if (QKeyValue.FindBoolAttribute(e.Attributes, "candidate"))
      {
        assume.Attributes = new QKeyValue(Token.NoToken, "candidate", new List<object>(), assume.Attributes);
        assume.Attributes.AddParam(this.callee);
      }

      #endregion

      if (callId is not null) {
        (assume as ICarriesAttributes).CopyIdWithModificationsFrom(tok, e,
          id => new TrackedCallEnsures(callId, id));
      }

      newBlockBody.Add(assume);
    }

    #endregion

    #region aouts := couts

    for (int i = 0, n = this.Outs.Count; i < n; i++)
    {
      if (this.Outs[i] != null)
      {
        Variable /*!*/
          param_i = cce.NonNull(this.Proc.OutParams[i]);
        Expr /*!*/
          cout_exp = new IdentifierExpr(cce.NonNull(couts[i]).tok, cce.NonNull(couts[i]));
        Contract.Assert(cout_exp != null);
        AssignCmd assign = Cmd.SimpleAssign(param_i.tok, cce.NonNull(this.Outs[i]), cout_exp);
        if (callId is not null) {
          Attributes = new QKeyValue(param_i.tok, "id", new List<object>(){ $"{callId}$out{i}" }, Attributes);
        }
        newBlockBody.Add(assign);
      }
    }

    #endregion

    #endregion

    return new StateCmd(this.tok, tempVars, newBlockBody);
  }

  class NameEqualityComparer : EqualityComparer<IdentifierExpr>
  {
    public override bool Equals(IdentifierExpr x, IdentifierExpr y)
    {
      return x.Name.Equals(y.Name);
    }

    public override int GetHashCode(IdentifierExpr obj)
    {
      return obj.Name.GetHashCode();
    }
  }

  NameEqualityComparer comparer = new NameEqualityComparer();

  public Substitution calleeSubstitution;
  public Substitution calleeSubstitutionOld;

  public IEnumerable<IdentifierExpr> UnmodifiedBefore(Procedure oldProcedure)
  {
    Contract.Requires(oldProcedure != null);

    return Proc.Modifies.Except(oldProcedure.Modifies, comparer)
      .Select(e => new IdentifierExpr(Token.NoToken, e.Decl));
  }

  public IEnumerable<IdentifierExpr> ModifiedBefore(Procedure oldProcedure)
  {
    Contract.Requires(oldProcedure != null);

    return oldProcedure.Modifies.Except(Proc.Modifies, comparer)
      .Select(e => new IdentifierExpr(Token.NoToken, e.Decl));
  }

  public Expr Postcondition(Procedure procedure, List<Expr> modifies, Dictionary<Variable, Expr> oldSubst,
    Program program, Func<Expr, Expr> extract)
  {
    Contract.Requires(calleeSubstitution != null && calleeSubstitutionOld != null && modifies != null &&
                      oldSubst != null && program != null && extract != null);

    Substitution substOldCombined = v =>
    {
      if (oldSubst.TryGetValue(v, out var s))
      {
        return s;
      }

      return calleeSubstitutionOld(v);
    };

    var clauses = procedure.Ensures.Select(e =>
      Substituter.FunctionCallReresolvingApplyReplacingOldExprs(calleeSubstitution, substOldCombined, e.Condition,
        program)).Concat(modifies);
    // TODO(wuestholz): Try extracting a function for each clause:
    // return Conjunction(clauses.Select(c => extract(c)));
    var conj = Expr.And(clauses, true);
    return conj != null ? extract(conj) : conj;
  }

  public Expr CheckedPrecondition(Procedure procedure, Program program, Func<Expr, Expr> extract)
  {
    Contract.Requires(calleeSubstitution != null && calleeSubstitutionOld != null && program != null &&
                      extract != null);

    var clauses = procedure.Requires.Where(r => !r.Free).Select(r =>
      Substituter.FunctionCallReresolvingApplyReplacingOldExprs(calleeSubstitution, calleeSubstitutionOld,
        r.Condition, program));
    // TODO(wuestholz): Try extracting a function for each clause:
    // return Conjunction(clauses.Select(c => extract(c)));
    var conj = Expr.And(clauses, true);
    return conj != null ? extract(conj) : conj;
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    //Contract.Requires(visitor != null);
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitCallCmd(this);
  }
}