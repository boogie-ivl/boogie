using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

public class VariableBindings
{
  public readonly IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/
    VCExprVarBindings;

  public readonly IDictionary<TypeVariable /*!*/, VCExpr /*!*/> /*!*/
    TypeVariableBindings;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullDictionaryAndValues(VCExprVarBindings));
    Contract.Invariant(Cce.NonNullDictionaryAndValues(TypeVariableBindings));
  }


  public VariableBindings(IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ vcExprVarBindings,
    IDictionary<TypeVariable /*!*/, VCExpr /*!*/> /*!*/ typeVariableBindings)
  {
    Contract.Requires(Cce.NonNullDictionaryAndValues(vcExprVarBindings));
    Contract.Requires(Cce.NonNullDictionaryAndValues(typeVariableBindings));
    this.VCExprVarBindings = vcExprVarBindings;
    this.TypeVariableBindings = typeVariableBindings;
  }

  public VariableBindings() :
    this(new Dictionary<VCExprVar /*!*/, VCExprVar /*!*/>(),
      new Dictionary<TypeVariable /*!*/, VCExpr /*!*/>())
  {
  }

  public VariableBindings Clone()
  {
    Contract.Ensures(Contract.Result<VariableBindings>() != null);
    IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/
      newVCExprVarBindings =
        new Dictionary<VCExprVar /*!*/, VCExprVar /*!*/>();
    foreach (KeyValuePair<VCExprVar /*!*/, VCExprVar /*!*/> pair in VCExprVarBindings)
    {
      Contract.Assert(Cce.NonNullElements(pair));
      newVCExprVarBindings.Add(pair);
    }

    IDictionary<TypeVariable /*!*/, VCExpr /*!*/> /*!*/
      newTypeVariableBindings =
        new Dictionary<TypeVariable /*!*/, VCExpr /*!*/>();
    foreach (KeyValuePair<TypeVariable /*!*/, VCExpr /*!*/> pair in TypeVariableBindings)
    {
      Contract.Assert(Cce.NonNullElements(pair));
      newTypeVariableBindings.Add(pair);
    }

    return new VariableBindings(newVCExprVarBindings, newTypeVariableBindings);
  }
}