using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

public abstract class OpTypeEraser : StandardVCExprOpVisitor<VCExpr /*!*/, VariableBindings /*!*/>
{
  protected readonly TypeAxiomBuilderIntBoolU /*!*/
    AxBuilder;

  protected readonly TypeEraser /*!*/
    Eraser;

  protected readonly VCExpressionGenerator /*!*/
    Gen;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(AxBuilder != null);
    Contract.Invariant(Eraser != null);
    Contract.Invariant(Gen != null);
  }


  public OpTypeEraser(TypeEraser /*!*/ eraser, TypeAxiomBuilderIntBoolU /*!*/ axBuilder,
    VCExpressionGenerator /*!*/ gen)
  {
    Contract.Requires(eraser != null);
    Contract.Requires(axBuilder != null);
    Contract.Requires(gen != null);
    this.AxBuilder = axBuilder;
    this.Eraser = eraser;
    this.Gen = gen;
  }

  protected override VCExpr StandardResult(VCExprNAry node, VariableBindings bindings)
  {
    //Contract.Requires(bindings != null);
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    System.Diagnostics.Debug.Fail("Don't know how to erase types in this expression: " + node);
    Contract.Assert(false);
    throw new Cce.UnreachableException(); // to please the compiler
  }

  private List<VCExpr /*!*/> /*!*/ MutateSeq(VCExprNAry node, VariableBindings bindings, int newPolarity)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
    int oldPolarity = Eraser.Polarity;
    Eraser.Polarity = newPolarity;
    List<VCExpr /*!*/> /*!*/
      newArgs = Eraser.MutateSeq(node.Arguments, bindings);
    Eraser.Polarity = oldPolarity;
    return newArgs;
  }

  private VCExpr CastArguments(VCExprNAry node, Type argType, VariableBindings bindings, int newPolarity)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(argType != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return Gen.Function(node.Op,
      AxBuilder.CastSeq(MutateSeq(node, bindings, newPolarity),
        argType));
  }

  // Cast the arguments of the node to their old type if necessary and possible; otherwise use
  // their new type (int, real, bool, or U)
  private VCExpr CastArgumentsToOldType(VCExprNAry node, VariableBindings bindings, int newPolarity)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Requires((node.Arity > 0));
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    List<VCExpr /*!*/> /*!*/
      newArgs = MutateSeq(node, bindings, newPolarity);
    Type /*!*/
      oldType = node[0].Type;
    if (AxBuilder.UnchangedType(oldType) &&
        node.Arguments.Skip(1).All(e => e.Type.Equals(oldType)))
    {
      return Gen.Function(node.Op, AxBuilder.CastSeq(newArgs, oldType));
    }
    else
    {
      return Gen.Function(node.Op, AxBuilder.CastSeq(newArgs, AxBuilder.U));
    }
  }

  ///////////////////////////////////////////////////////////////////////////

  public override VCExpr VisitNotOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, Type.Bool, bindings, -Eraser.Polarity);
  }

  public override VCExpr VisitEqOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitNeqOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitImpliesOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    // UGLY: the code for tracking polarities should be factored out
    List<VCExpr /*!*/> /*!*/
      newArgs = new List<VCExpr /*!*/>(2);
    Eraser.Polarity = -Eraser.Polarity;
    newArgs.Add(Eraser.Mutate(node[0], bindings));
    Eraser.Polarity = -Eraser.Polarity;
    newArgs.Add(Eraser.Mutate(node[1], bindings));
    return Gen.Function(node.Op, AxBuilder.CastSeq(newArgs, Type.Bool));
  }

  public override VCExpr VisitDistinctOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitIfThenElseOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    List<VCExpr /*!*/> /*!*/
      newArgs = MutateSeq(node, bindings, 0);
    newArgs[0] = AxBuilder.Cast(newArgs[0], Type.Bool);
    Type t = node.Type;
    if (!AxBuilder.UnchangedType(t))
    {
      t = AxBuilder.U;
    }

    newArgs[1] = AxBuilder.Cast(newArgs[1], t);
    newArgs[2] = AxBuilder.Cast(newArgs[2], t);
    return Gen.Function(node.Op, newArgs);
  }

  public override VCExpr /*!*/ VisitCustomOp(VCExprNAry /*!*/ node, VariableBindings /*!*/ bindings)
  {
    Contract.Requires(node != null);
    Contract.Requires(bindings != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    List<VCExpr /*!*/> /*!*/
      newArgs = MutateSeq(node, bindings, 0);
    return Gen.Function(node.Op, newArgs);
  }

  public override VCExpr VisitAddOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, node.Type, bindings, 0);
  }

  public override VCExpr VisitSubOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, node.Type, bindings, 0);
  }

  public override VCExpr VisitMulOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, node.Type, bindings, 0);
  }

  public override VCExpr VisitDivOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, Type.Int, bindings, 0);
  }

  public override VCExpr VisitModOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, Type.Int, bindings, 0);
  }

  public override VCExpr VisitRealDivOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, Type.Real, bindings, 0);
  }

  /*public override VCExpr VisitFloatDivOp(VCExprNAry node, VariableBindings bindings)
    {
      Contract.Requires((bindings != null));
      Contract.Requires((node != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return CastArguments(node, Type.Float, bindings, 0);
    }*/
  public override VCExpr VisitPowOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, Type.Real, bindings, 0);
  }

  public override VCExpr VisitLtOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitLeOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitGtOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitGeOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitSubtypeOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArguments(node, AxBuilder.U, bindings, 0);
  }

  public override VCExpr VisitToIntOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitToRealOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatAddOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatSubOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatMulOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatDivOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatLeqOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatLtOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatGeqOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatGtOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatEqOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitFloatNeqOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitBvOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitBvExtractOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return CastArgumentsToOldType(node, bindings, 0);
  }

  public override VCExpr VisitBvConcatOp(VCExprNAry node, VariableBindings bindings)
  {
    Contract.Requires((bindings != null));
    Contract.Requires((node != null));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    List<VCExpr /*!*/> /*!*/
      newArgs = MutateSeq(node, bindings, 0);

    // each argument is cast to its old type
    Contract.Assert(newArgs.Count == node.Arity && newArgs.Count == 2);
    VCExpr /*!*/
      arg0 = AxBuilder.Cast(newArgs[0], node[0].Type);
    Contract.Assert(arg0 != null);
    VCExpr /*!*/
      arg1 = AxBuilder.Cast(newArgs[1], node[1].Type);
    Contract.Assert(arg1 != null);
    return Gen.Function(node.Op, arg0, arg1);
  }
}