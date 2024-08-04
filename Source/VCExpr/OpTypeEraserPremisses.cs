using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

public class OpTypeEraserPremisses : OpTypeEraser
{
  private TypeAxiomBuilderPremisses /*!*/
    AxBuilderPremisses;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(AxBuilderPremisses != null);
  }


  public OpTypeEraserPremisses(TypeEraserPremisses eraser, TypeAxiomBuilderPremisses axBuilder,
    VCExpressionGenerator gen)
    : base(eraser, axBuilder, gen)
  {
    Contract.Requires(gen != null);
    Contract.Requires(axBuilder != null);
    Contract.Requires(eraser != null);
    this.AxBuilderPremisses = axBuilder;
  }

  private VCExpr HandleFunctionOp(Function newFun, List<Type /*!*/> /*!*/ typeArgs /*!*/,
    IEnumerable<VCExpr /*!*/> /*!*/ oldArgs, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(newFun != null);
    Contract.Requires(Cce.NonNullElements(typeArgs /*!*/));
    Contract.Requires(Cce.NonNullElements(oldArgs));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    // UGLY: the code for tracking polarities should be factored out
    int oldPolarity = Eraser.Polarity;
    Eraser.Polarity = 0;

    List<VCExpr /*!*/> /*!*/
      newArgs = new List<VCExpr /*!*/>(typeArgs.Count);

    // translate the explicit type arguments
    foreach (Type /*!*/ t in typeArgs)
    {
      Contract.Assert(t != null);
      newArgs.Add(AxBuilder.Type2Term(t, bindings.TypeVariableBindings));
    }

    // recursively translate the value arguments
    foreach (VCExpr /*!*/ arg in oldArgs)
    {
      Contract.Assert(arg != null);
      Type /*!*/
        newType = Cce.NonNull(newFun.InParams[newArgs.Count]).TypedIdent.Type;
      newArgs.Add(AxBuilder.Cast(Eraser.Mutate(arg, bindings), newType));
    }

    Eraser.Polarity = oldPolarity;
    return Gen.Function(newFun, newArgs);
  }

  public override VCExpr /*!*/ VisitSelectOp(VCExprNAry /*!*/ node,
    VariableBindings /*!*/ bindings)
  {
    Contract.Requires(node != null);
    Contract.Requires(bindings != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    MapType /*!*/
      mapType = node[0].Type.AsMap;
    Contract.Assert(mapType != null);
    Function /*!*/
      select =
        AxBuilder.MapTypeAbstracter.Select(mapType, out var instantiations);
    Contract.Assert(select != null);

    List<int> /*!*/
      explicitTypeParams =
        AxBuilderPremisses.MapTypeAbstracterPremisses
          .ExplicitSelectTypeParams(mapType);
    Contract.Assert(select.InParams.Count == explicitTypeParams.Count + node.Arity);

    List<Type /*!*/> /*!*/
      typeArgs = new List<Type /*!*/>(explicitTypeParams.Count);
    foreach (int i in explicitTypeParams)
    {
      typeArgs.Add(node.TypeArguments[i]);
    }

    return HandleFunctionOp(select, typeArgs, node.Arguments, bindings);
  }

  public override VCExpr VisitStoreOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    Function /*!*/
      store =
        AxBuilder.MapTypeAbstracter.Store(node[0].Type.AsMap, out var instantiations);
    Contract.Assert(store != null);
    return HandleFunctionOp(store,
      // the store function never has explicit
      // type parameters
      new List<Type /*!*/>(),
      node.Arguments, bindings);
  }

  public override VCExpr VisitBoogieFunctionOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    Function /*!*/
      oriFun = ((VCExprBoogieFunctionOp) node.Op).Func;
    Contract.Assert(oriFun != null);
    UntypedFunction untypedFun = AxBuilderPremisses.Typed2Untyped(oriFun);
    Contract.Assert(untypedFun.Fun.InParams.Count ==
                    untypedFun.ExplicitTypeParams.Count + node.Arity);

    List<Type /*!*/> /*!*/
      typeArgs =
        ExtractTypeArgs(node,
          oriFun.TypeParameters, untypedFun.ExplicitTypeParams);
    return HandleFunctionOp(untypedFun.Fun, typeArgs, node.Arguments, bindings);
  }

  private List<Type /*!*/> /*!*/ ExtractTypeArgs(VCExprNAry node, List<TypeVariable> allTypeParams,
    List<TypeVariable /*!*/> /*!*/ explicitTypeParams)
  {
    Contract.Requires(allTypeParams != null);
    Contract.Requires(node != null);
    Contract.Requires(Cce.NonNullElements(explicitTypeParams));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Type>>()));
    List<Type /*!*/> /*!*/
      res = new List<Type /*!*/>(explicitTypeParams.Count);
    foreach (TypeVariable /*!*/ var in explicitTypeParams)
    {
      Contract.Assert(var != null);
      // this lookup could be optimised
      res.Add(node.TypeArguments[allTypeParams.IndexOf(var)]);
    }

    return res;
  }
}