using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

// different classes for erasing complex types in VCExprs, replacing them
// with axioms that can be handled by theorem provers and SMT solvers

namespace Microsoft.Boogie.TypeErasure
{
  // some functionality that is needed in many places (and that should
  // really be provided by the Spec# container classes; maybe one
  // could integrate the functions in a nicer way?)

  //////////////////////////////////////////////////////////////////////////////

  internal struct TypeCtorRepr
  {
    // function that represents the application of the type constructor
    // to smaller types
    public readonly Function /*!*/
      Ctor;

    // left-inverse functions that extract the subtypes of a compound type
    public readonly List<Function /*!*/> /*!*/
      Dtors;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Ctor != null);
      Contract.Invariant(Cce.NonNullElements(Dtors));
    }


    public TypeCtorRepr(Function ctor, List<Function /*!*/> /*!*/ dtors)
    {
      Contract.Requires(ctor != null);
      Contract.Requires(Cce.NonNullElements(dtors));
      Contract.Requires(ctor.InParams.Count == dtors.Count);
      this.Ctor = ctor;
      this.Dtors = dtors;
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // The class responsible for creating and keeping track of all
  // axioms related to the type system. This abstract class is made
  // concrete in two subclasses, one for type erasure with type
  // premisses in quantifiers (the semantic approach), and one for
  // type erasure with explicit type arguments of polymorphic
  // functions (the syntactic approach).

  [ContractClassFor(typeof(TypeAxiomBuilder))]
  public abstract class TypeAxiomBuilderContracts : TypeAxiomBuilder
  {
    public TypeAxiomBuilderContracts()
      : base((VCExpressionGenerator) null)
    {
    }

    internal override MapTypeAbstractionBuilder MapTypeAbstracter
    {
      get
      {
        Contract.Ensures(Contract.Result<MapTypeAbstractionBuilder>() != null);
        throw new NotImplementedException();
      }
    }

    public override Type TypeAfterErasure(Type type)
    {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public override bool UnchangedType(Type type)
    {
      Contract.Requires(type != null);
      throw new NotImplementedException();
    }

    protected override void AddVarTypeAxiom(VCExprVar var, Type originalType)
    {
      Contract.Requires(var != null);
      Contract.Requires(originalType != null);
      throw new NotImplementedException();
    }

    public override object Clone()
    {
      Contract.Ensures(Contract.Result<object>() != null);

      throw new NotImplementedException();
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // Subclass of the TypeAxiomBuilder that provides all functionality
  // to deal with native sorts of a theorem prover (that are the only
  // types left after erasing all other types). Currently, these are:
  //
  //  U ... sort of all individuals/objects/values
  //  T ... sort of all types
  //  int ... integers
  //  bool ... booleans

  [ContractClass(typeof(TypeAxiomBuilderIntBoolUContracts))]
  public abstract class TypeAxiomBuilderIntBoolU : TypeAxiomBuilder
  {
    public TypeAxiomBuilderIntBoolU(VCExpressionGenerator gen)
      : base(gen)
    {
      Contract.Requires(gen != null);

      TypeCasts = new Dictionary<Type /*!*/, TypeCastSet>();
    }

    // constructor to allow cloning
    internal TypeAxiomBuilderIntBoolU(TypeAxiomBuilderIntBoolU builder)
      : base(builder)
    {
      Contract.Requires(builder != null);

      TypeCasts = new Dictionary<Type /*!*/, TypeCastSet>(builder.TypeCasts);
    }

    public override void Setup(List<Type> usedTypes)
    {
      base.Setup(usedTypes);

      foreach (var ty in usedTypes) {
        GetTypeCasts(ty);
      }
    }

    // generate inverse axioms for casts (castToU(castFromU(x)) = x, under certain premisses)
    protected abstract VCExpr /*!*/ GenReverseCastAxiom(Function /*!*/ castToU, Function /*!*/ castFromU);

    protected VCExpr GenReverseCastEq(Function castToU, Function castFromU, out VCExprVar var,
      out List<VCTrigger /*!*/> /*!*/ triggers)
    {
      Contract.Requires((castFromU != null));
      Contract.Requires((castToU != null));
      Contract.Ensures((Cce.NonNullElements(Contract.ValueAtReturn(out triggers))));
      Contract.Ensures(Contract.ValueAtReturn(out var) != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      var = Gen.Variable("x", U);

      VCExpr inner = Gen.Function(castFromU, var);
      VCExpr lhs = Gen.Function(castToU, inner);
      triggers = HelperFuns.ToList(Gen.Trigger(true, HelperFuns.ToList(inner)));

      return Gen.Eq(lhs, var);
    }

    protected abstract VCExpr /*!*/ GenCastTypeAxioms(Function /*!*/ castToU, Function /*!*/ castFromU);

    ///////////////////////////////////////////////////////////////////////////
    // storage of type casts for types that are supposed to be left over in the
    // VCs (like int, bool, bitvectors)

    private readonly IDictionary<Type /*!*/, TypeCastSet /*!*/> /*!*/
      TypeCasts;

    [ContractInvariantMethod]
    void TypeCastsInvariantMethod()
    {
      Contract.Invariant(TypeCasts != null);
    }

    private TypeCastSet GetTypeCasts(Type type)
    {
      Contract.Requires(type != null);
      if (!TypeCasts.TryGetValue(type, out var res))
      {
        Function /*!*/
          castToU = HelperFuns.BoogieFunction(type.ToString() + "_2_U", type, U);
        Function /*!*/
          castFromU = HelperFuns.BoogieFunction("U_2_" + type.ToString(), U, type);

        AddTypeAxiom(GenLeftInverseAxiom(castToU, castFromU, 0));
        AddTypeAxiom(GenReverseCastAxiom(castToU, castFromU));
        AddTypeAxiom(GenCastTypeAxioms(castToU, castFromU));

        res = new TypeCastSet(castToU, castFromU);
        TypeCasts.Add(type, res);
      }

      return res;
    }

    [Pure]
    public Function CastTo(Type type)
    {
      Contract.Requires(type != null);
      Contract.Requires(UnchangedType(type));
      Contract.Ensures(Contract.Result<Function>() != null);
      return GetTypeCasts(type).CastFromU;
    }

    public Function CastFrom(Type type)
    {
      Contract.Requires(type != null);
      Contract.Requires((UnchangedType(type)));
      Contract.Ensures(Contract.Result<Function>() != null);
      return GetTypeCasts(type).CastToU;
    }

    private struct TypeCastSet
    {
      public readonly Function /*!*/
        CastToU;

      public readonly Function /*!*/
        CastFromU;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(CastToU != null);
        Contract.Invariant(CastFromU != null);
      }


      public TypeCastSet(Function castToU, Function castFromU)
      {
        Contract.Requires(castFromU != null);
        Contract.Requires(castToU != null);
        CastToU = castToU;
        CastFromU = castFromU;
      }
    }

    public bool IsCast(Function fun)
    {
      Contract.Requires(fun != null);
      if (fun.InParams.Count != 1)
      {
        return false;
      }

      Type /*!*/
        inType = Cce.NonNull(fun.InParams[0]).TypedIdent.Type;
      if (inType.Equals(U))
      {
        Type /*!*/
          outType = Cce.NonNull(fun.OutParams[0]).TypedIdent.Type;
        if (!TypeCasts.ContainsKey(outType))
        {
          return false;
        }

        return fun.Equals(CastTo(outType));
      }
      else
      {
        if (!TypeCasts.ContainsKey(inType))
        {
          return false;
        }

        Type /*!*/
          outType = Cce.NonNull(fun.OutParams[0]).TypedIdent.Type;
        if (!outType.Equals(U))
        {
          return false;
        }

        return fun.Equals(CastFrom(inType));
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    // the only types that we allow in "untyped" expressions are U,
    // Type.Int, Type.Real, Type.Bool, and Type.RMode

    public override Type TypeAfterErasure(Type type)
    {
      //Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      if (UnchangedType(type))
      {
        // these types are kept
        return type;
      }
      else
      {
        // all other types are replaced by U
        return U;
      }
    }

    [Pure]
    public override bool UnchangedType(Type type)
    {
      //Contract.Requires(type != null);
      return type.IsInt || type.IsReal || type.IsBool || type.IsBv || type.IsFloat || type.IsRMode || type.IsString ||
             type.IsRegEx;
    }

    public override VCExpr Cast(VCExpr expr, Type toType)
    {
      Contract.Requires(toType != null);
      Contract.Requires(expr != null);
      Contract.Requires((expr.Type.Equals(U) || UnchangedType(expr.Type)));
      Contract.Requires((toType.Equals(U) || UnchangedType(toType)));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (expr.Type.Equals(toType))
      {
        return expr;
      }

      if (toType.Equals(U))
      {
        return Gen.Function(CastFrom(expr.Type), expr);
      }
      else
      {
        Contract.Assert(expr.Type.Equals(U));
        return Gen.Function(CastTo(toType), expr);
      }
    }

    public List<VCExpr /*!*/> /*!*/ CastSeq(List<VCExpr /*!*/> /*!*/ exprs, Type toType)
    {
      Contract.Requires(toType != null);
      Contract.Requires(Cce.NonNullElements(exprs));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      List<VCExpr /*!*/> /*!*/
        res = new List<VCExpr /*!*/>(exprs.Count);
      foreach (VCExpr /*!*/ expr in exprs)
      {
        Contract.Assert(expr != null);
        res.Add(Cast(expr, toType));
      }

      return res;
    }
  }

  [ContractClassFor(typeof(TypeAxiomBuilderIntBoolU))]
  public abstract class TypeAxiomBuilderIntBoolUContracts : TypeAxiomBuilderIntBoolU
  {
    public TypeAxiomBuilderIntBoolUContracts()
      : base((TypeAxiomBuilderIntBoolU) null)
    {
    }

    protected override VCExpr GenReverseCastAxiom(Function castToU, Function castFromU)
    {
      Contract.Requires(castToU != null);
      Contract.Requires(castFromU != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      throw new NotImplementedException();
    }

    protected override VCExpr GenCastTypeAxioms(Function castToU, Function castFromU)
    {
      Contract.Requires(castFromU != null);
      Contract.Requires(castToU != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      throw new NotImplementedException();
    }

    internal override MapTypeAbstractionBuilder MapTypeAbstracter
    {
      get { throw new NotImplementedException(); }
    }

    protected override void AddVarTypeAxiom(VCExprVar var, Type originalType)
    {
      throw new NotImplementedException();
    }

    public override object Clone()
    {
      throw new NotImplementedException();
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Class for computing most general abstractions of map types. An abstraction
  // of a map type t is a maptype t' in which closed proper subtypes have been replaced
  // with type variables. E.g., an abstraction of <a>[C a, int]a would be <a>[C a, b]a.
  // We subsequently consider most general abstractions as ordinary parametrised types,
  // i.e., "<a>[C a, b]a" would be considered as a type "M b" with polymorphically typed
  // access functions
  //
  //            select<a,b>(M b, C a, b) returns (a)
  //            store<a,b>(M b, C a, b, a) returns (M b)

  [ContractClassFor(typeof(MapTypeAbstractionBuilder))]
  internal abstract class MapTypeAbstractionBuilderContracts : MapTypeAbstractionBuilder
  {
    public MapTypeAbstractionBuilderContracts()
      : base(null, null)
    {
    }

    protected override void GenSelectStoreFunctions(MapType abstractedType, TypeCtorDecl synonymDecl,
      out Function select, out Function store)
    {
      Contract.Requires(abstractedType != null);
      Contract.Requires(synonymDecl != null);
      Contract.Ensures(Contract.ValueAtReturn(out select) != null);
      Contract.Ensures(Contract.ValueAtReturn(out store) != null);

      throw new NotImplementedException();
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////

  // The central class for turning types VCExprs into untyped
  // VCExprs. This class makes use of the type axiom builder to manage
  // the available types and symbols.


  //////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////
}