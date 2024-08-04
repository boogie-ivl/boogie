using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

[ContractClass(typeof(TypeAxiomBuilderContracts))]
public abstract class TypeAxiomBuilder : ICloneable
{
  protected readonly VCExpressionGenerator /*!*/
    Gen;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Gen != null);
    Contract.Invariant(Ctor != null);
  }


  internal abstract MapTypeAbstractionBuilder /*!*/ MapTypeAbstracter { get; }

  ///////////////////////////////////////////////////////////////////////////
  // Type Axioms

  // list in which all typed axioms are collected
  private readonly List<VCExpr /*!*/> /*!*/
    AllTypeAxioms;

  [ContractInvariantMethod]
  void AllTypeAxiomsInvariantMethod()
  {
    Contract.Invariant(Cce.NonNullElements(AllTypeAxioms));
  }

  // list in which type axioms are incrementally collected
  private readonly List<VCExpr /*!*/> /*!*/
    IncTypeAxioms;

  [ContractInvariantMethod]
  void IncTypeAxiomsInvariantMethod()
  {
    Contract.Invariant(Cce.NonNullElements(IncTypeAxioms));
  }

  internal void AddTypeAxiom(VCExpr axiom)
  {
    Contract.Requires(axiom != null);
    AllTypeAxioms.Add(axiom);
    IncTypeAxioms.Add(axiom);
  }

  // Return all axioms that were added since the last time NewAxioms
  // was called
  public VCExpr GetNewAxioms()
  {
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    VCExpr /*!*/
      res = Gen.NAry(VCExpressionGenerator.AndOp, IncTypeAxioms);
    IncTypeAxioms.Clear();
    return res;
  }

  // mapping from a type to its constructor number/index
  private readonly Function /*!*/
    Ctor;

  private BigNum CurrentCtorNum;

  private VCExpr GenCtorAssignment(VCExpr typeRepr)
  {
    Contract.Requires(typeRepr != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    VCExpr res = Gen.Eq(Gen.Function(Ctor, typeRepr),
      Gen.Integer(CurrentCtorNum));
    CurrentCtorNum = CurrentCtorNum + BigNum.ONE;
    return res;
  }

  private VCExpr GenCtorAssignment(Function typeRepr)
  {
    Contract.Requires(typeRepr != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    List<VCExprVar /*!*/> /*!*/
      quantifiedVars = HelperFuns.GenVarsForInParams(typeRepr, Gen);
    VCExpr /*!*/
      eq =
        GenCtorAssignment(Gen.Function(typeRepr,
          HelperFuns.ToVCExprList(quantifiedVars)));

    if (typeRepr.InParams.Count == 0)
    {
      return eq;
    }

    return Gen.Forall(quantifiedVars, new List<VCTrigger /*!*/>(),
      "ctor:" + typeRepr.Name, 1, eq);
  }

  // generate an axiom (forall x0, x1, ... :: invFun(fun(x0, x1, ...) == xi)
  protected VCExpr GenLeftInverseAxiom(Function fun, Function invFun, int dtorNum)
  {
    Contract.Requires(invFun != null);
    Contract.Requires(fun != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    List<VCExprVar /*!*/> /*!*/
      quantifiedVars = HelperFuns.GenVarsForInParams(fun, Gen);
    Contract.Assert(Cce.NonNullElements(quantifiedVars));

    VCExpr /*!*/
      funApp = Gen.Function(fun, HelperFuns.ToVCExprList(quantifiedVars));
    VCExpr /*!*/
      lhs = Gen.Function(invFun, funApp);
    VCExpr /*!*/
      rhs = quantifiedVars[dtorNum];
    VCExpr /*!*/
      eq = Gen.Eq(lhs, rhs);

    List<VCTrigger /*!*/> /*!*/
      triggers = HelperFuns.ToList(Gen.Trigger(true, HelperFuns.ToList(funApp)));
    Contract.Assert(Cce.NonNullElements(triggers));
    return Gen.Forall(quantifiedVars, triggers, "typeInv:" + invFun.Name, 1, eq);
  }

  ///////////////////////////////////////////////////////////////////////////

  // the type of everything that is not int, bool, or a type
  [ContractInvariantMethod]
  void ObjectInvariant2()
  {
    Contract.Invariant(UDecl != null);
    Contract.Invariant(TDecl != null);
    Contract.Invariant(U != null);
    Contract.Invariant(T != null);
  }

  private readonly TypeCtorDecl /*!*/
    UDecl;

  public readonly Type /*!*/
    U;

  // the type of types
  private readonly TypeCtorDecl /*!*/
    TDecl;

  public readonly Type /*!*/
    T;

  public abstract Type /*!*/ TypeAfterErasure(Type /*!*/ type);

  [Pure]
  public abstract bool UnchangedType(Type /*!*/ type);

  ///////////////////////////////////////////////////////////////////////////
  // Symbols for representing types

  private readonly IDictionary<Type /*!*/, VCExpr /*!*/> /*!*/
    BasicTypeReprs;

  [ContractInvariantMethod]
  void BasicTypeReprsInvariantMethod()
  {
    Contract.Invariant(Cce.NonNullDictionaryAndValues(BasicTypeReprs));
  }

  private VCExpr GetBasicTypeRepr(Type type)
  {
    Contract.Requires(type != null);
    Contract.Requires(type.IsBasic || type.IsBv || type.IsFloat);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    if (!BasicTypeReprs.TryGetValue(type, out var res))
    {
      res = Gen.Function(HelperFuns.BoogieFunction(type.ToString() + "Type", T));
      AddTypeAxiom(GenCtorAssignment(res));
      BasicTypeReprs.Add(type, res);
    }

    return Cce.NonNull(res);
  }

  private readonly IDictionary<TypeCtorDecl /*!*/, TypeCtorRepr /*!*/> /*!*/
    TypeCtorReprs;

  [ContractInvariantMethod]
  void TypeCtorReprsInvariantMethod()
  {
    Contract.Invariant(TypeCtorReprs != null);
  }

  internal TypeCtorRepr GetTypeCtorReprStruct(TypeCtorDecl decl)
  {
    Contract.Requires(decl != null);
    if (!TypeCtorReprs.TryGetValue(decl, out var reprSet))
    {
      Function /*!*/
        ctor = HelperFuns.UniformBoogieFunction(decl.Name + "Type", decl.Arity, T);
      Contract.Assert(ctor != null);
      AddTypeAxiom(GenCtorAssignment(ctor));

      List<Function /*!*/> /*!*/
        dtors = new List<Function /*!*/>(decl.Arity);
      for (int i = 0; i < decl.Arity; ++i)
      {
        Function /*!*/
          dtor = HelperFuns.UniformBoogieFunction(decl.Name + "TypeInv" + i, 1, T);
        dtors.Add(dtor);
        AddTypeAxiom(GenLeftInverseAxiom(ctor, dtor, i));
      }

      reprSet = new TypeCtorRepr(ctor, dtors);
      TypeCtorReprs.Add(decl, reprSet);
    }

    return reprSet;
  }

  public Function GetTypeCtorRepr(TypeCtorDecl decl)
  {
    Contract.Requires(decl != null);
    Contract.Ensures(Contract.Result<Function>() != null);
    return GetTypeCtorReprStruct(decl).Ctor;
  }

  public Function GetTypeDtor(TypeCtorDecl decl, int num)
  {
    Contract.Requires(decl != null);
    Contract.Ensures(Contract.Result<Function>() != null);
    return GetTypeCtorReprStruct(decl).Dtors[num];
  }

  // mapping from free type variables to VCExpr variables
  private readonly IDictionary<TypeVariable /*!*/, VCExprVar /*!*/> /*!*/
    TypeVariableMapping;

  [ContractInvariantMethod]
  void TypeVariableMappingInvariantMethod()
  {
    Contract.Invariant(Cce.NonNullDictionaryAndValues(TypeVariableMapping));
  }

  public VCExprVar Typed2Untyped(TypeVariable var)
  {
    Contract.Requires(var != null);
    Contract.Ensures(Contract.Result<VCExprVar>() != null);
    if (!TypeVariableMapping.TryGetValue(var, out var res))
    {
      res = new VCExprVar(var.Name, T);
      TypeVariableMapping.Add(var, res);
    }

    return Cce.NonNull(res);
  }


  ////////////////////////////////////////////////////////////////////////////
  // Symbols for representing variables and constants

  // Globally defined variables
  private readonly IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/
    Typed2UntypedVariables;

  [ContractInvariantMethod]
  void Typed2UntypedVariablesInvariantMethod()
  {
    Contract.Invariant(Cce.NonNullDictionaryAndValues(Typed2UntypedVariables));
  }

  // This method must only be used for free (unbound) variables
  public VCExprVar Typed2Untyped(VCExprVar var)
  {
    Contract.Requires(var != null);
    Contract.Ensures(Contract.Result<VCExprVar>() != null);
    VCExprVar res = TryTyped2Untyped(var);
    if (res == null)
    {
      res = Gen.Variable(var.Name, TypeAfterErasure(var.Type));
      Typed2UntypedVariables.Add(var, res);
      AddVarTypeAxiom(res, var.Type);
    }

    return Cce.NonNull(res);
  }

  /// <summary>
  ///  This method is like Typed2Untyped, except in the case where the given variables
  ///  doesn't exist in the mapping.  For that case, this method returns null whereas
  ///  Typed2Untyped creates a new variable that it adds to the mapping.
  /// </summary>
  /// <param name="var"></param>
  /// <returns></returns>
  public VCExprVar TryTyped2Untyped(VCExprVar var)
  {
    Contract.Requires(var != null);
    if (Typed2UntypedVariables.TryGetValue(var, out var res))
    {
      return res;
    }
    else
    {
      return null;
    }
  }

  protected abstract void AddVarTypeAxiom(VCExprVar /*!*/ var, Type /*!*/ originalType);

  ///////////////////////////////////////////////////////////////////////////
  // Translation function from types to their term representation

  public VCExpr Type2Term(Type type, IDictionary<TypeVariable /*!*/, VCExpr /*!*/> /*!*/ varMapping)
  {
    Contract.Requires(type != null);
    Contract.Requires(Cce.NonNullDictionaryAndValues(varMapping));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    //
    if (type.IsBasic || type.IsBv || type.IsFloat)
    {
      //
      return GetBasicTypeRepr(type);
      //
    }
    else if (type.IsCtor)
    {
      //
      CtorType ctype = type.AsCtor;
      Function /*!*/
        repr = GetTypeCtorRepr(ctype.Decl);
      List<VCExpr /*!*/> /*!*/
        args = new List<VCExpr /*!*/>(ctype.Arguments.Count);
      foreach (Type /*!*/ t in ctype.Arguments.ToArray())
      {
        Contract.Assert(t != null);
        args.Add(Type2Term(t, varMapping));
      }

      return Gen.Function(repr, args);
      //
    }
    else if (type.IsVariable)
    {
      //
      if (!varMapping.TryGetValue(type.AsVariable, out var res))
      {
        // then the variable is free and we bind it at this point to a term
        // variable
        res = Typed2Untyped(type.AsVariable);
      }

      return Cce.NonNull(res);
      //
    }
    else if (type.IsMap)
    {
      //
      return Type2Term(MapTypeAbstracter.AbstractMapType(type.AsMap), varMapping);
      //
    }
    else
    {
      System.Diagnostics.Debug.Fail("Don't know how to handle this type: " + type);
      Contract.Assert(false);
      throw new Cce.UnreachableException(); // please the compiler
    }
  }

  ////////////////////////////////////////////////////////////////////////////

  public TypeAxiomBuilder(VCExpressionGenerator gen)
  {
    Contract.Requires(gen != null);
    this.Gen = gen;
    AllTypeAxioms = new List<VCExpr /*!*/>();
    IncTypeAxioms = new List<VCExpr /*!*/>();
    BasicTypeReprs = new Dictionary<Type /*!*/, VCExpr /*!*/>();
    CurrentCtorNum = BigNum.ZERO;
    TypeCtorReprs = new Dictionary<TypeCtorDecl /*!*/, TypeCtorRepr>();
    TypeVariableMapping = new Dictionary<TypeVariable /*!*/, VCExprVar /*!*/>();
    Typed2UntypedVariables = new Dictionary<VCExprVar /*!*/, VCExprVar /*!*/>();

    TypeCtorDecl /*!*/
      uDecl = new TypeCtorDecl(Token.NoToken, "U", 0);
    UDecl = uDecl;
    Type /*!*/
      u = new CtorType(Token.NoToken, uDecl, new List<Type>());
    U = u;

    TypeCtorDecl /*!*/
      tDecl = new TypeCtorDecl(Token.NoToken, "T", 0);
    TDecl = tDecl;
    Type /*!*/
      t = new CtorType(Token.NoToken, tDecl, new List<Type>());
    T = t;

    Ctor = HelperFuns.BoogieFunction("Ctor", t, Type.Int);
  }

  public virtual void Setup(List<Type> usedTypes)
  {
    foreach (var ty in usedTypes) {
      GetBasicTypeRepr(ty);
    }
  }

  // constructor to allow cloning
  internal TypeAxiomBuilder(TypeAxiomBuilder builder)
  {
    Contract.Requires(builder != null);
    Gen = builder.Gen;
    AllTypeAxioms = new List<VCExpr /*!*/>(builder.AllTypeAxioms);
    IncTypeAxioms = new List<VCExpr /*!*/>(builder.IncTypeAxioms);

    UDecl = builder.UDecl;
    U = builder.U;

    TDecl = builder.TDecl;
    T = builder.T;

    Ctor = builder.Ctor;
    CurrentCtorNum = builder.CurrentCtorNum;

    BasicTypeReprs = new Dictionary<Type /*!*/, VCExpr /*!*/>(builder.BasicTypeReprs);
    TypeCtorReprs = new Dictionary<TypeCtorDecl /*!*/, TypeCtorRepr>(builder.TypeCtorReprs);

    TypeVariableMapping =
      new Dictionary<TypeVariable /*!*/, VCExprVar /*!*/>(builder.TypeVariableMapping);
    Typed2UntypedVariables =
      new Dictionary<VCExprVar /*!*/, VCExprVar /*!*/>(builder.Typed2UntypedVariables);
  }

  public abstract Object /*!*/ Clone();
    
  public abstract VCExpr Cast(VCExpr expr, Type toType);
}