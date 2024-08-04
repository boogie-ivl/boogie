using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

[ContractClass(typeof(TypeEraserContracts))]
public abstract class TypeEraser : MutatingVCExprVisitor<VariableBindings /*!*/>
{
  protected readonly TypeAxiomBuilderIntBoolU /*!*/
    AxBuilder;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(AxBuilder != null);
  }


  protected abstract OpTypeEraser /*!*/ OpEraser { get; }

  ////////////////////////////////////////////////////////////////////////////

  public TypeEraser(TypeAxiomBuilderIntBoolU axBuilder, VCExpressionGenerator gen)
    : base(gen)
  {
    Contract.Requires(gen != null);
    Contract.Requires(axBuilder != null);
    AxBuilder = axBuilder;
  }

  public VCExpr Erase(VCExpr expr, int polarity)
  {
    Contract.Requires(expr != null);
    Contract.Requires((polarity >= -1 && polarity <= 1));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    this.Polarity = polarity;
    return Mutate(expr, new VariableBindings());
  }

  internal int Polarity = 1; // 1 for positive, -1 for negative, 0 for both

  ////////////////////////////////////////////////////////////////////////////

  public override VCExpr Visit(VCExprLiteral node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    Contract.Assume(node.Type == Type.Bool || node.Type == Type.Int || node.Type == Type.Real ||
                    node.Type == Type.RMode || node.Type == Type.String || node.Type == Type.RegEx);
    return node;
  }

  ////////////////////////////////////////////////////////////////////////////

  public override bool AvoidVisit(VCExprNAry node, VariableBindings arg)
  {
    return node.Op.Equals(VCExpressionGenerator.AndOp) ||
           node.Op.Equals(VCExpressionGenerator.OrOp);
  }

  public override VCExpr Visit(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    VCExprOp /*!*/
      op = node.Op;
    if (op == VCExpressionGenerator.AndOp || op == VCExpressionGenerator.OrOp)
    {
      // more efficient on large conjunctions/disjunctions
      return base.Visit(node, bindings);
    }

    // the visitor that handles all other operators
    return node.Accept<VCExpr /*!*/, VariableBindings /*!*/>(OpEraser, bindings);
  }

  // this method is called by MutatingVCExprVisitor.Visit(VCExprNAry, ...)
  protected override VCExpr /*!*/ UpdateModifiedNode(VCExprNAry /*!*/ originalNode,
    List<VCExpr /*!*/> /*!*/ newSubExprs, bool changed, VariableBindings /*!*/ bindings)
  {
    //Contract.Requires(originalNode != null);
    //Contract.Requires(cce.NonNullElements(newSubExprs));
    //Contract.Requires(bindings != null);
    Contract.Assume(originalNode.Op == VCExpressionGenerator.AndOp ||
                    originalNode.Op == VCExpressionGenerator.OrOp);
    return Gen.Function(originalNode.Op,
      AxBuilder.Cast(newSubExprs[0], Type.Bool),
      AxBuilder.Cast(newSubExprs[1], Type.Bool));
  }

  ////////////////////////////////////////////////////////////////////////////

  public override VCExpr Visit(VCExprVar node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    if (!bindings.VCExprVarBindings.TryGetValue(node, out var res))
    {
      return AxBuilder.Typed2Untyped(node);
    }

    return Cce.NonNull(res);
  }

  ////////////////////////////////////////////////////////////////////////////

  protected bool IsUniversalQuantifier(VCExprQuantifier node)
  {
    Contract.Requires(node != null);
    return Polarity == 1 && node.Quan == Quantifier.EX ||
           Polarity == -1 && node.Quan == Quantifier.ALL;
  }

  protected List<VCExprVar /*!*/> /*!*/ BoundVarsAfterErasure(List<VCExprVar /*!*/> /*!*/ oldBoundVars,
    // the mapping between old and new variables
    // is added to this bindings-object
    VariableBindings /*!*/ bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(Cce.NonNullElements(oldBoundVars));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));

    List<VCExprVar /*!*/> /*!*/
      newBoundVars = new List<VCExprVar /*!*/>(oldBoundVars.Count);
    foreach (VCExprVar /*!*/ var in oldBoundVars)
    {
      Type /*!*/
        newType = AxBuilder.TypeAfterErasure(var.Type);
      VCExprVar /*!*/
        newVar = Gen.Variable(var.Name, newType);
      newBoundVars.Add(newVar);
      bindings.VCExprVarBindings.Add(var, newVar);
    }

    return newBoundVars;
  }

  // We check whether casts Int2U or Bool2U on the bound variables
  // occur in triggers. In case a trigger like f(Int2U(x)) occurs,
  // it may be better to give variable x the type U and remove the
  // cast. The following method returns true if the quantifier
  // should be translated again with a different typing
  protected bool RedoQuantifier(VCExprQuantifier /*!*/ node,
    VCExprQuantifier /*!*/ newNode,
    // the bound vars that actually occur in the body or
    // in any of the triggers
    List<VCExprVar /*!*/> /*!*/ occurringVars,
    VariableBindings /*!*/ oldBindings,
    out VariableBindings /*!*/ newBindings,
    out List<VCExprVar /*!*/> /*!*/ newBoundVars)
  {
    Contract.Requires(node != null);
    Contract.Requires(newNode != null);
    Contract.Requires(Cce.NonNullElements(occurringVars));
    Contract.Requires(oldBindings != null);
    Contract.Ensures(Contract.ValueAtReturn(out newBindings) != null);
    Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out newBoundVars)));
    List<VCExprVar /*!*/> castVariables =
      VariableCastCollector.FindCastVariables(node, newNode, AxBuilder);
    if (castVariables.Count == 0)
    {
      newBindings = oldBindings; // to make the compiler happy
      newBoundVars = newNode.BoundVars; // to make the compiler happy
      return false;
    }

    // redo everything with a different typing ...

    newBindings = oldBindings.Clone();
    newBoundVars = new List<VCExprVar /*!*/>(node.BoundVars.Count);
    foreach (VCExprVar /*!*/ var in node.BoundVars)
    {
      Contract.Assert(var != null);
      Type /*!*/
        newType =
          castVariables.Contains(var)
            ? AxBuilder.U
            : AxBuilder.TypeAfterErasure(var.Type);
      Contract.Assert(newType != null);
      VCExprVar /*!*/
        newVar = Gen.Variable(var.Name, newType);
      Contract.Assert(newVar != null);
      newBoundVars.Add(newVar);
      newBindings.VCExprVarBindings.Add(var, newVar);
    }

    return true;
  }

  ////////////////////////////////////////////////////////////////////////////

  public override VCExpr Visit(VCExprLet node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    VariableBindings /*!*/
      newVarBindings = bindings.Clone();

    List<VCExprVar /*!*/> /*!*/
      newBoundVars = new List<VCExprVar /*!*/>(node.BoundVars.Count);
    foreach (VCExprVar /*!*/ var in node.BoundVars)
    {
      Type /*!*/
        newType = AxBuilder.TypeAfterErasure(var.Type);
      VCExprVar /*!*/
        newVar = Gen.Variable(var.Name, newType);
      newBoundVars.Add(newVar);
      newVarBindings.VCExprVarBindings.Add(var, newVar);
    }

    List<VCExprLetBinding /*!*/> /*!*/
      newbindings = new List<VCExprLetBinding /*!*/>(node.Length);
    for (int i = 0; i < node.Length; ++i)
    {
      VCExprLetBinding /*!*/
        binding = node[i];
      Contract.Assert(binding != null);
      VCExprVar /*!*/
        newVar = newBoundVars[i];
      Type /*!*/
        newType = newVar.Type;

      VCExpr /*!*/
        newE = AxBuilder.Cast(Mutate(binding.E, newVarBindings), newType);
      newbindings.Add(Gen.LetBinding(newVar, newE));
    }

    VCExpr /*!*/
      newbody = Mutate(node.Body, newVarBindings);
    return Gen.Let(newbindings, newbody);
  }
}