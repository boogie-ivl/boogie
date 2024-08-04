using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

// Erasure of types using premisses   (forall x :: type(x)=T ==> p(x))

namespace Microsoft.Boogie.TypeErasure
{
  // When using type premisses, we can distinguish two kinds of type
  // parameters of a function or map: parameters that occur in the
  // formal argument types of the function are "implicit" because they
  // can be inferred from the actual argument types; parameters that
  // only occur in the result type of the function are "explicit"
  // because they are not inferrable and have to be given to the
  // function as additional arguments.
  //
  // The following structure is used to store the untyped version of a
  // typed function, together with the lists of implicit and explicit
  // type parameters (in the same order as they occur in the signature
  // of the original function).

  internal struct UntypedFunction
  {
    public readonly Function /*!*/
      Fun;

    // type parameters that can be extracted from the value parameters
    public readonly List<TypeVariable /*!*/> /*!*/
      ImplicitTypeParams;

    // type parameters that have to be given explicitly
    public readonly List<TypeVariable /*!*/> /*!*/
      ExplicitTypeParams;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Fun != null);
      Contract.Invariant(Cce.NonNullElements(ImplicitTypeParams));
      Contract.Invariant(Cce.NonNullElements(ExplicitTypeParams));
    }


    public UntypedFunction(Function /*!*/ fun,
      List<TypeVariable /*!*/> /*!*/ implicitTypeParams,
      List<TypeVariable /*!*/> /*!*/ explicitTypeParams)
    {
      Contract.Requires(fun != null);
      Contract.Requires(Cce.NonNullElements(implicitTypeParams));
      Contract.Requires(Cce.NonNullElements(explicitTypeParams));
      Fun = fun;
      ImplicitTypeParams = implicitTypeParams;
      ExplicitTypeParams = explicitTypeParams;
    }
  }

  public class TypeAxiomBuilderPremisses : TypeAxiomBuilderIntBoolU
  {
    private const string TypeName = "type";
    static TypeAxiomBuilderPremisses() {
      ScopedNamer.AddBoogieDeterminedName(TypeName);
    }
    public CoreOptions Options { get; }

    public TypeAxiomBuilderPremisses(VCExpressionGenerator gen, CoreOptions options)
      : base(gen)
    {
      Contract.Requires(gen != null);
      this.Options = options;

      TypeFunction = HelperFuns.BoogieFunction("dummy", Type.Int);
      Typed2UntypedFunctions = new Dictionary<Function /*!*/, UntypedFunction>();
      MapTypeAbstracterAttr = null;
    }

    // constructor to allow cloning
    [NotDelayed]
    internal TypeAxiomBuilderPremisses(TypeAxiomBuilderPremisses builder)
      : base(builder)
    {
      Contract.Requires(builder != null);
      this.Options = builder.Options;
      TypeFunction = builder.TypeFunction;
      Typed2UntypedFunctions =
        new Dictionary<Function /*!*/, UntypedFunction>(builder.Typed2UntypedFunctions);

      MapTypeAbstracterAttr =
        builder.MapTypeAbstracterAttr == null
          ? null
          : new MapTypeAbstractionBuilderPremisses(this, builder.Gen, builder.MapTypeAbstracterAttr);
    }

    public override Object Clone()
    {
      Contract.Ensures(Contract.Result<Object>() != null);
      return new TypeAxiomBuilderPremisses(this);
    }

    public override void Setup(List<Type> usedTypes)
    {
      TypeFunction = HelperFuns.BoogieFunction(TypeName, U, T);
      base.Setup(usedTypes);
    }

    ////////////////////////////////////////////////////////////////////////////

    // generate axioms of the kind "forall x:U. {Int2U(U2Int(x))}
    //                                          type(x)=int ==> Int2U(U2Int(x))==x"
    protected override VCExpr GenReverseCastAxiom(Function castToU, Function castFromU)
    {
      //Contract.Requires(castFromU != null);
      //Contract.Requires(castToU != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr /*!*/
        eq = GenReverseCastEq(castToU, castFromU, out var var, out var triggers);
      Contract.Assert(Cce.NonNullElements(triggers));
      Contract.Assert(var != null);
      Contract.Assert(eq != null);
      VCExpr /*!*/
        premiss;
      premiss = GenVarTypeAxiom(var, Cce.NonNull(castFromU.OutParams[0]).TypedIdent.Type,
        // we don't have any bindings available
        new Dictionary<TypeVariable /*!*/, VCExpr /*!*/>());
      VCExpr /*!*/
        matrix = Gen.ImpliesSimp(premiss, eq);
      Contract.Assert(matrix != null);
      return Gen.Forall(HelperFuns.ToList(var), triggers, "cast:" + castFromU.Name, 1, matrix);
    }

    protected override VCExpr GenCastTypeAxioms(Function castToU, Function castFromU)
    {
      //Contract.Requires(castFromU != null);
      //Contract.Requires(castToU != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Type /*!*/
        fromType = Cce.NonNull(castToU.InParams[0]).TypedIdent.Type;
      return GenFunctionAxiom(castToU, new List<TypeVariable /*!*/>(), new List<TypeVariable /*!*/>(),
        HelperFuns.ToList(fromType), fromType);
    }

    private MapTypeAbstractionBuilderPremisses MapTypeAbstracterAttr;

    internal override MapTypeAbstractionBuilder /*!*/ MapTypeAbstracter
    {
      get
      {
        Contract.Ensures(Contract.Result<MapTypeAbstractionBuilder>() != null);

        if (MapTypeAbstracterAttr == null)
        {
          MapTypeAbstracterAttr = new MapTypeAbstractionBuilderPremisses(this, Gen);
        }

        return MapTypeAbstracterAttr;
      }
    }

    internal MapTypeAbstractionBuilderPremisses /*!*/ MapTypeAbstracterPremisses
    {
      get
      {
        Contract.Ensures(Contract.Result<MapTypeAbstractionBuilderPremisses>() != null);

        return (MapTypeAbstractionBuilderPremisses) MapTypeAbstracter;
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    // function that maps individuals to their type
    // the field is overwritten with its actual value in "Setup"
    private Function /*!*/
      TypeFunction;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(TypeFunction != null);
    }


    public VCExpr TypeOf(VCExpr expr)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Gen.Function(TypeFunction, expr);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Generate type premisses and type parameter bindings for quantifiers, functions, procedures

    // let-bindings to extract the instantiations of type parameters
    public List<VCExprLetBinding /*!*/> /*!*/
      GenTypeParamBindings( // the original bound variables and (implicit) type parameters
        List<TypeVariable /*!*/> /*!*/ typeParams, List<VCExprVar /*!*/> /*!*/ oldBoundVars,
        // VariableBindings to which the translation
        // TypeVariable -> VCExprVar is added
        VariableBindings /*!*/ bindings,
        bool addTypeVarsToBindings)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(Cce.NonNullElements(oldBoundVars));
      Contract.Requires(bindings != null);

      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprLetBinding>>()));

      // type variables are replaced with ordinary variables that are bound using a
      // let-expression
      if (addTypeVarsToBindings)
      {
        foreach (TypeVariable /*!*/ tvar in typeParams)
        {
          Contract.Assert(tvar != null);
          bindings.TypeVariableBindings.Add(tvar, Gen.Variable(tvar.Name, T));
        }
      }

      // extract the values of type variables from the term variables
      List<VCExprVar /*!*/> /*!*/
        UtypedVars = new List<VCExprVar /*!*/>(oldBoundVars.Count);
      List<Type /*!*/> /*!*/
        originalTypes = new List<Type /*!*/>(oldBoundVars.Count);
      foreach (VCExprVar var in oldBoundVars)
      {
        VCExprVar /*!*/
          newVar = bindings.VCExprVarBindings[var];
        if (newVar.Type.Equals(U))
        {
          UtypedVars.Add(newVar);
          originalTypes.Add(var.Type);
        }
      }

      UtypedVars.TrimExcess();
      originalTypes.TrimExcess();

      return BestTypeVarExtractors(typeParams, originalTypes, UtypedVars, bindings);
    }


    public VCExpr /*!*/ AddTypePremisses(List<VCExprLetBinding /*!*/> /*!*/ typeVarBindings,
      VCExpr /*!*/ typePremisses, bool universal,
      VCExpr /*!*/ body)
    {
      Contract.Requires(Cce.NonNullElements(typeVarBindings));
      Contract.Requires(typePremisses != null);
      Contract.Requires(body != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExpr /*!*/
        bodyWithPremisses;
      if (universal)
      {
        bodyWithPremisses = Gen.ImpliesSimp(typePremisses, body);
      }
      else
      {
        bodyWithPremisses = Gen.AndSimp(typePremisses, body);
      }

      return Gen.Let(typeVarBindings, bodyWithPremisses);
    }


    ///////////////////////////////////////////////////////////////////////////
    // Extract the instantiations of type variables from the concrete types of
    // term variables. E.g., for a function  f<a>(x : C a), we would extract the
    // instantiation of "a" by looking at the concrete type of "x".

    public List<VCExprLetBinding /*!*/> /*!*/
      BestTypeVarExtractors(List<TypeVariable /*!*/> /*!*/ vars, List<Type /*!*/> /*!*/ types,
        List<VCExprVar /*!*/> /*!*/ concreteTypeSources,
        VariableBindings /*!*/ bindings)
    {
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Requires(Cce.NonNullElements(types));
      Contract.Requires(Cce.NonNullElements(concreteTypeSources));
      Contract.Requires(bindings != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprLetBinding>>()));

      List<VCExprLetBinding /*!*/> /*!*/
        typeParamBindings = new List<VCExprLetBinding /*!*/>();
      foreach (TypeVariable /*!*/ var in vars)
      {
        Contract.Assert(var != null);
        VCExpr extractor = BestTypeVarExtractor(var, types, concreteTypeSources);
        if (extractor != null)
        {
          typeParamBindings.Add(
            Gen.LetBinding((VCExprVar) bindings.TypeVariableBindings[var],
              extractor));
        }
      }

      return typeParamBindings;
    }

    private VCExpr BestTypeVarExtractor(TypeVariable /*!*/ var, List<Type /*!*/> /*!*/ types,
      List<VCExprVar /*!*/> /*!*/ concreteTypeSources)
    {
      Contract.Requires(var != null);
      Contract.Requires(Cce.NonNullElements(types));
      Contract.Requires(Cce.NonNullElements(concreteTypeSources));
      List<VCExpr /*!*/> allExtractors = TypeVarExtractors(var, types, concreteTypeSources);
      Contract.Assert(Cce.NonNullElements(allExtractors));
      if (allExtractors.Count == 0)
      {
        return null;
      }

      VCExpr bestExtractor = allExtractors[0];
      int bestExtractorSize = SizeComputingVisitor.ComputeSize(bestExtractor);
      for (int i = 1; i < allExtractors.Count; ++i)
      {
        int newSize = SizeComputingVisitor.ComputeSize(allExtractors[i]);
        if (newSize < bestExtractorSize)
        {
          bestExtractor = allExtractors[i];
          bestExtractorSize = newSize;
        }
      }

      return bestExtractor;
    }

    private List<VCExpr /*!*/> /*!*/ TypeVarExtractors(TypeVariable /*!*/ var, List<Type /*!*/> /*!*/ types,
      List<VCExprVar /*!*/> /*!*/ concreteTypeSources)
    {
      Contract.Requires(var != null);
      Contract.Requires(Cce.NonNullElements(types));
      Contract.Requires(Cce.NonNullElements(concreteTypeSources));
      Contract.Requires((types.Count == concreteTypeSources.Count));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      List<VCExpr /*!*/> /*!*/
        res = new List<VCExpr /*!*/>();
      for (int i = 0; i < types.Count; ++i)
      {
        TypeVarExtractors(var, types[i], TypeOf(concreteTypeSources[i]), res);
      }

      return res;
    }

    private void TypeVarExtractors(TypeVariable var, Type completeType, VCExpr innerTerm,
      List<VCExpr /*!*/> /*!*/ extractors)
    {
      Contract.Requires(innerTerm != null);
      Contract.Requires(completeType != null);
      Contract.Requires(var != null);
      Contract.Requires(Cce.NonNullElements(extractors));
      if (completeType.IsVariable)
      {
        if (var.Equals(completeType))
        {
          extractors.Add(innerTerm);
        } // else nothing
      }
      else if (completeType.IsBasic)
      {
        // nothing
      }
      else if (completeType.IsCtor)
      {
        CtorType /*!*/
          ctorType = completeType.AsCtor;
        if (ctorType.Arguments.Count > 0)
        {
          // otherwise there are no chances of extracting any
          // instantiations from this type
          TypeCtorRepr repr = GetTypeCtorReprStruct(ctorType.Decl);
          for (int i = 0; i < ctorType.Arguments.Count; ++i)
          {
            VCExpr /*!*/
              newInnerTerm = Gen.Function(repr.Dtors[i], innerTerm);
            Contract.Assert(newInnerTerm != null);
            TypeVarExtractors(var, ctorType.Arguments[i], newInnerTerm, extractors);
          }
        }
      }
      else if (completeType.IsMap)
      {
        TypeVarExtractors(var, MapTypeAbstracter.AbstractMapType(completeType.AsMap),
          innerTerm, extractors);
      }
      else
      {
        System.Diagnostics.Debug.Fail("Don't know how to handle this type: " + completeType);
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Symbols for representing functions

    // Globally defined functions
    private readonly IDictionary<Function /*!*/, UntypedFunction /*!*/> /*!*/
      Typed2UntypedFunctions;

    [ContractInvariantMethod]
    void Typed2UntypedFunctionsInvariantMethod()
    {
      Contract.Invariant(Typed2UntypedFunctions != null);
    }

    // distinguish between implicit and explicit type parameters
    internal static void SeparateTypeParams(List<Type /*!*/> /*!*/ valueArgumentTypes,
      List<TypeVariable> /*!*/ allTypeParams,
      out List<TypeVariable /*!*/> /*!*/ implicitParams,
      out List<TypeVariable /*!*/> /*!*/ explicitParams)
    {
      Contract.Requires(Cce.NonNullElements(valueArgumentTypes));
      Contract.Requires(allTypeParams != null);
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out implicitParams)));
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out explicitParams)));
      List<TypeVariable> /*!*/
        varsInInParamTypes = new List<TypeVariable>();
      foreach (Type /*!*/ t in valueArgumentTypes)
      {
        Contract.Assert(t != null);
        varsInInParamTypes.AppendWithoutDups(t.FreeVariables);
      }

      implicitParams = new List<TypeVariable /*!*/>(allTypeParams.Count);
      explicitParams = new List<TypeVariable /*!*/>(allTypeParams.Count);

      foreach (TypeVariable /*!*/ var in allTypeParams)
      {
        Contract.Assert(var != null);
        if (varsInInParamTypes.Contains(var))
        {
          implicitParams.Add(var);
        }
        else
        {
          explicitParams.Add(var);
        }
      }

      implicitParams.TrimExcess();
      explicitParams.TrimExcess();
    }

    internal UntypedFunction Typed2Untyped(Function fun)
    {
      Contract.Requires(fun != null);
      if (!Typed2UntypedFunctions.TryGetValue(fun, out var res))
      {
        Contract.Assert(fun.OutParams.Count == 1);

        // if all of the parameters are int or bool, the function does
        // not have to be changed
        if (fun.InParams.All(param => UnchangedType(Cce.NonNull(param).TypedIdent.Type)) &&
            UnchangedType(Cce.NonNull(fun.OutParams[0]).TypedIdent.Type) &&
            fun.TypeParameters.Count == 0)
        {
          res = new UntypedFunction(fun, new List<TypeVariable /*!*/>(), new List<TypeVariable /*!*/>());
        }
        else
        {
          List<Type /*!*/> /*!*/
            argTypes = new List<Type /*!*/>();
          foreach (Variable /*!*/ v in fun.InParams)
          {
            Contract.Assert(v != null);
            argTypes.Add(v.TypedIdent.Type);
          }

          SeparateTypeParams(argTypes, fun.TypeParameters, out var implicitParams, out var explicitParams);

          Type[] /*!*/
            types = new Type[explicitParams.Count + fun.InParams.Count + 1];
          int i = 0;
          for (int j = 0; j < explicitParams.Count; ++j)
          {
            types[i] = T;
            i = i + 1;
          }

          for (int j = 0; j < fun.InParams.Count; ++i, ++j)
          {
            types[i] = TypeAfterErasure(Cce.NonNull(fun.InParams[j]).TypedIdent.Type);
          }

          types[types.Length - 1] = TypeAfterErasure(Cce.NonNull(fun.OutParams[0]).TypedIdent.Type);

          Function /*!*/
            untypedFun = HelperFuns.BoogieFunction(fun.Name, types);
          Contract.Assert(untypedFun != null);
          untypedFun.Attributes = fun.Attributes;
          res = new UntypedFunction(untypedFun, implicitParams, explicitParams);
          if (U.Equals(types[types.Length - 1]))
          {
            AddTypeAxiom(GenFunctionAxiom(res, fun));
          }
        }

        Typed2UntypedFunctions.Add(fun, res);
      }

      return res;
    }

    private VCExpr GenFunctionAxiom(UntypedFunction fun, Function originalFun)
    {
      Contract.Requires(originalFun != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      List<Type /*!*/> /*!*/
        originalInTypes = new List<Type /*!*/>(originalFun.InParams.Count);
      foreach (Formal /*!*/ f in originalFun.InParams)
      {
        originalInTypes.Add(f.TypedIdent.Type);
      }

      return GenFunctionAxiom(fun.Fun, fun.ImplicitTypeParams, fun.ExplicitTypeParams,
        originalInTypes,
        Cce.NonNull(originalFun.OutParams[0]).TypedIdent.Type);
    }

    internal VCExpr /*!*/ GenFunctionAxiom(Function /*!*/ fun,
      List<TypeVariable /*!*/> /*!*/ implicitTypeParams,
      List<TypeVariable /*!*/> /*!*/ explicitTypeParams,
      List<Type /*!*/> /*!*/ originalInTypes,
      Type /*!*/ originalResultType)
    {
      Contract.Requires(Cce.NonNullElements(implicitTypeParams));
      Contract.Requires(fun != null);
      Contract.Requires(Cce.NonNullElements(explicitTypeParams));
      Contract.Requires(Cce.NonNullElements(originalInTypes));
      Contract.Requires(originalResultType != null);
      Contract.Requires(originalInTypes.Count + explicitTypeParams.Count == fun.InParams.Count);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<VCExprVar /*!*/> /*!*/
        typedInputVars = new List<VCExprVar /*!*/>(originalInTypes.Count);
      int i = 0;
      foreach (Type /*!*/ t in originalInTypes)
      {
        Contract.Assert(t != null);
        typedInputVars.Add(Gen.Variable("arg" + i, t));
        i = i + 1;
      }

      VariableBindings /*!*/
        bindings = new VariableBindings();

      // type parameters that have to be given explicitly are replaced
      // with universally quantified type variables
      List<VCExprVar /*!*/> /*!*/
        boundVars = new List<VCExprVar /*!*/>(explicitTypeParams.Count + typedInputVars.Count);
      foreach (TypeVariable /*!*/ var in explicitTypeParams)
      {
        Contract.Assert(var != null);
        VCExprVar /*!*/
          newVar = Gen.Variable(var.Name, T);
        boundVars.Add(newVar);
        bindings.TypeVariableBindings.Add(var, newVar);
      }

      // bound term variables are replaced with bound term variables typed in
      // a simpler way
      foreach (VCExprVar /*!*/ var in typedInputVars)
      {
        Contract.Assert(var != null);
        Type /*!*/
          newType = TypeAfterErasure(var.Type);
        Contract.Assert(newType != null);
        VCExprVar /*!*/
          newVar = Gen.Variable(var.Name, newType);
        Contract.Assert(newVar != null);
        boundVars.Add(newVar);
        bindings.VCExprVarBindings.Add(var, newVar);
      }

      List<VCExprLetBinding /*!*/> typeVarBindings =
        GenTypeParamBindings(implicitTypeParams, typedInputVars, bindings, true);
      Contract.Assert(Cce.NonNullElements(typeVarBindings));
      List<VCExpr> boundVarExprs = HelperFuns.ToVCExprList(boundVars);

      VCExpr /*!*/
        funApp = Gen.Function(fun, boundVarExprs);
      Contract.Assert(funApp != null);
      VCExpr /*!*/
        conclusion = Gen.Eq(TypeOf(funApp),
          Type2Term(originalResultType, bindings.TypeVariableBindings));
      Contract.Assert(conclusion != null);

      // Create `(= (type var) ...)` premises for each U-type argument
      var typePremisses =
        boundVarExprs
          .Where(e => e.Type.Equals(U))
          .Select((e, i) => Gen.Eq(TypeOf(e), Type2Term(originalInTypes[i], bindings.TypeVariableBindings)))
          .Aggregate(VCExpressionGenerator.True, (e1, e2) => Gen.AndSimp(e1, e2));
      VCExpr conclusionWithPremisses =
          AddTypePremisses(typeVarBindings, typePremisses, true, conclusion);

      if (boundVars.Count > 0)
      {
        List<VCTrigger /*!*/> triggers = HelperFuns.ToList(Gen.Trigger(true, HelperFuns.ToList(funApp)));
        Contract.Assert(Cce.NonNullElements(triggers));
        return Gen.Forall(boundVars, triggers, "funType:" + fun.Name, 1, conclusionWithPremisses);
      }
      else
      {
        return conclusionWithPremisses;
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    protected override void AddVarTypeAxiom(VCExprVar var, Type originalType)
    {
      //Contract.Requires(originalType != null);
      //Contract.Requires(var != null);
      AddTypeAxiom(GenVarTypeAxiom(var, originalType,
        // we don't have any bindings available
        new Dictionary<TypeVariable /*!*/, VCExpr /*!*/>()));
    }

    public VCExpr GenVarTypeAxiom(VCExprVar var, Type originalType,
      IDictionary<TypeVariable /*!*/, VCExpr /*!*/> /*!*/ varMapping)
    {
      Contract.Requires(var != null);
      Contract.Requires(originalType != null);
      Contract.Requires(Cce.NonNullDictionaryAndValues(varMapping));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (!var.Type.Equals(originalType))
      {
        VCExpr /*!*/
          typeRepr = Type2Term(originalType, varMapping);
        return Gen.Eq(TypeOf(var), typeRepr);
      }

      return VCExpressionGenerator.True;
    }
  }

  /////////////////////////////////////////////////////////////////////////////

  internal class MapTypeAbstractionBuilderPremisses : MapTypeAbstractionBuilder
  {
    private readonly TypeAxiomBuilderPremisses /*!*/ AxBuilderPremisses;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(AxBuilderPremisses != null);
    }


    internal MapTypeAbstractionBuilderPremisses(TypeAxiomBuilderPremisses axBuilder, VCExpressionGenerator gen)
      : base(axBuilder, gen)
    {
      Contract.Requires(gen != null);
      Contract.Requires(axBuilder != null);

      this.AxBuilderPremisses = axBuilder;
    }

    // constructor for cloning
    internal MapTypeAbstractionBuilderPremisses(TypeAxiomBuilderPremisses axBuilder, VCExpressionGenerator gen,
      MapTypeAbstractionBuilderPremisses builder)
      : base(axBuilder, gen, builder)
    {
      Contract.Requires(builder != null);
      Contract.Requires(gen != null);
      Contract.Requires(axBuilder != null);

      this.AxBuilderPremisses = axBuilder;
    }

    ////////////////////////////////////////////////////////////////////////////

    // Determine the type parameters of a map type that have to be
    // given explicitly when applying the select function (the
    // parameters that only occur in the result type of the
    // map). These parameters are given as a list of indexes sorted in
    // ascending order; the index i refers to the i'th bound variable
    // in a type    <a0, a1, ..., an>[...]...
    public List<int> /*!*/ ExplicitSelectTypeParams(MapType type)
    {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<List<int>>() != null);

      if (!explicitSelectTypeParamsCache.TryGetValue(type, out var res))
      {
        TypeAxiomBuilderPremisses.SeparateTypeParams(type.Arguments.ToList(),
          type.TypeParameters,
          out var implicitParams,
          out var explicitParams);
        res = new List<int>(explicitParams.Count);
        foreach (TypeVariable /*!*/ var in explicitParams)
        {
          Contract.Assert(var != null);
          res.Add(type.TypeParameters.IndexOf(var));
        }

        explicitSelectTypeParamsCache.Add(type, res);
      }

      return Cce.NonNull(res);
    }

    private IDictionary<MapType /*!*/, List<int> /*!*/> /*!*/
      explicitSelectTypeParamsCache =
        new Dictionary<MapType /*!*/, List<int> /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvarant()
    {
      Contract.Invariant(Cce.NonNullDictionaryAndValues(explicitSelectTypeParamsCache));
    }


    ////////////////////////////////////////////////////////////////////////////

    protected override void GenSelectStoreFunctions(MapType abstractedType, TypeCtorDecl synonym,
      out Function /*!*/ select, out Function /*!*/ store)
    {
      //Contract.Requires(synonym != null);
      //Contract.Requires(abstractedType != null);
      Contract.Ensures(Contract.ValueAtReturn(out select) != null);
      Contract.Ensures(Contract.ValueAtReturn(out store) != null);
      GenTypeAxiomParams(abstractedType, synonym, out var mapTypeSynonym,
        out var typeParams, out var originalInTypes);

      // select
      select = CreateAccessFun(typeParams, originalInTypes,
        abstractedType.Result, synonym.Name + "Select",
        out var implicitSelectParams, out var explicitSelectParams);

      // store, which gets one further argument: the assigned rhs
      originalInTypes.Add(abstractedType.Result);

      store = CreateAccessFun(typeParams, originalInTypes,
        mapTypeSynonym, synonym.Name + "Store",
        out var implicitStoreParams, out var explicitStoreParams);

      // the store function does not have any explicit type parameters
      Contract.Assert(explicitStoreParams.Count == 0);

      AxBuilder.AddTypeAxiom(GenMapAxiom0(select, store, abstractedType.Result, implicitSelectParams,
        explicitSelectParams, originalInTypes));
      AxBuilder.AddTypeAxiom(GenMapAxiom1(select, store, abstractedType.Result, explicitSelectParams));
    }

    protected void GenTypeAxiomParams(MapType /*!*/ abstractedType, TypeCtorDecl /*!*/ synonymDecl,
      out Type /*!*/ mapTypeSynonym,
      out List<TypeVariable /*!*/> /*!*/ typeParams,
      out List<Type /*!*/> /*!*/ originalIndexTypes)
    {
      Contract.Requires(abstractedType != null);
      Contract.Requires(synonymDecl != null);
      Contract.Ensures(Contract.ValueAtReturn(out mapTypeSynonym) != null);
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out typeParams)));
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out originalIndexTypes)));
      typeParams = new List<TypeVariable /*!*/>();
      typeParams.AddRange(abstractedType.TypeParameters);
      typeParams.AddRange(abstractedType.FreeVariables);

      originalIndexTypes = new List<Type /*!*/>(abstractedType.Arguments.Count + 1);
      List<Type> /*!*/
        mapTypeParams = new List<Type>();
      foreach (TypeVariable /*!*/ var in abstractedType.FreeVariables)
      {
        Contract.Assert(var != null);
        mapTypeParams.Add(var);
      }

      mapTypeSynonym = new CtorType(Token.NoToken, synonymDecl, mapTypeParams);

      originalIndexTypes.Add(mapTypeSynonym);
      originalIndexTypes.AddRange(abstractedType.Arguments.ToList());
    }

    // method to actually create the select or store function
    private Function /*!*/ CreateAccessFun(List<TypeVariable /*!*/> /*!*/ originalTypeParams,
      List<Type /*!*/> /*!*/ originalInTypes,
      Type /*!*/ originalResult,
      string /*!*/ name,
      out List<TypeVariable /*!*/> /*!*/ implicitTypeParams, out List<TypeVariable /*!*/> /*!*/ explicitTypeParams)
    {
      Contract.Requires(Cce.NonNullElements(originalTypeParams));
      Contract.Requires(Cce.NonNullElements(originalInTypes));
      Contract.Requires(originalResult != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out implicitTypeParams)));
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out explicitTypeParams)));

      // select and store are basically handled like normal functions: the type
      // parameters are split into the implicit parameters, and into the parameters
      // that have to be given explicitly
      TypeAxiomBuilderPremisses.SeparateTypeParams(originalInTypes,
        new List<TypeVariable>(originalTypeParams),
        out implicitTypeParams,
        out explicitTypeParams);

      Type[] /*!*/
        ioTypes = new Type[explicitTypeParams.Count + originalInTypes.Count + 1];
      int i = 0;
      for (; i < explicitTypeParams.Count; ++i)
      {
        ioTypes[i] = AxBuilder.T;
      }

      foreach (Type /*!*/ type in originalInTypes)
      {
        Contract.Assert(type != null);
        ioTypes[i] = AxBuilder.U;
        i++;
      }

      ioTypes[i] = AxBuilder.U;

      Function /*!*/
        res = HelperFuns.BoogieFunction(name, ioTypes);
      Contract.Assert(res != null);

      if (AxBuilder.U.Equals(ioTypes[i]))
      {
        AxBuilder.AddTypeAxiom(
          AxBuilderPremisses.GenFunctionAxiom(res,
            implicitTypeParams, explicitTypeParams,
            originalInTypes, originalResult));
      }

      return res;
    }

    ///////////////////////////////////////////////////////////////////////////
    // The normal axioms of the theory of arrays (without extensionality)

    private VCExpr /*!*/ Select(Function /*!*/ select,
      // in general, the select function has to
      // receive explicit type parameters (which
      // are here already represented as VCExpr
      // of type T)
      List<VCExpr /*!*/> /*!*/ typeParams,
      VCExpr /*!*/ map,
      List<VCExprVar /*!*/> /*!*/ indexes)
    {
      Contract.Requires(select != null);
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Requires(map != null);
      Contract.Requires(Cce.NonNullElements(indexes));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<VCExpr /*!*/> /*!*/
        selectArgs = new List<VCExpr /*!*/>(typeParams.Count + indexes.Count + 1);
      selectArgs.AddRange(typeParams);
      selectArgs.Add(map);
      selectArgs.AddRange(HelperFuns.ToVCExprList(indexes));
      return Gen.Function(select, selectArgs);
    }

    private VCExpr Store(Function store, VCExpr map, List<VCExprVar /*!*/> /*!*/ indexes, VCExpr val)
    {
      Contract.Requires(val != null);
      Contract.Requires(map != null);
      Contract.Requires(store != null);
      Contract.Requires(Cce.NonNullElements(indexes));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      List<VCExpr /*!*/> /*!*/
        storeArgs = new List<VCExpr /*!*/>(indexes.Count + 2);
      storeArgs.Add(map);
      storeArgs.AddRange(HelperFuns.ToVCExprList(indexes));
      storeArgs.Add(val);
      return Gen.Function(store, storeArgs);
    }

    /// <summary>
    /// Generate:
    ///   (forall m, indexes, val ::
    ///     type(val) == T ==>
    ///     select(store(m, indexes, val), indexes) == val)
    /// where the quantifier body is also enclosed in a let that defines portions of T, if needed.
    /// </summary>
    private VCExpr GenMapAxiom0(Function select, Function store, Type mapResult,
      List<TypeVariable /*!*/> /*!*/ implicitTypeParamsSelect, List<TypeVariable /*!*/> /*!*/ explicitTypeParamsSelect,
      List<Type /*!*/> /*!*/ originalInTypes)
    {
      Contract.Requires(mapResult != null);
      Contract.Requires(store != null);
      Contract.Requires(select != null);
      Contract.Requires(Cce.NonNullElements(implicitTypeParamsSelect));
      Contract.Requires(Cce.NonNullElements(originalInTypes));
      Contract.Requires(Cce.NonNullElements(explicitTypeParamsSelect));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      int arity = store.InParams.Count - 2;
      List<VCExprVar /*!*/> inParams = new List<VCExprVar /*!*/>();
      List<VCExprVar /*!*/> quantifiedVars = new List<VCExprVar /*!*/>(store.InParams.Count);
      VariableBindings bindings = new VariableBindings();

      // bound variable:  m
      VCExprVar typedM = Gen.Variable("m", originalInTypes[0]);
      VCExprVar m = Gen.Variable("m", AxBuilder.U);
      inParams.Add(typedM);
      quantifiedVars.Add(m);
      bindings.VCExprVarBindings.Add(typedM, m);

      // bound variables:  indexes
      List<Type /*!*/> origIndexTypes = new List<Type /*!*/>(arity);
      List<Type /*!*/> indexTypes = new List<Type /*!*/>(arity);
      for (int i = 1; i < store.InParams.Count - 1; i++)
      {
        origIndexTypes.Add(originalInTypes[i]);
        indexTypes.Add(Cce.NonNull(store.InParams[i]).TypedIdent.Type);
      }

      Contract.Assert(arity == indexTypes.Count);
      List<VCExprVar /*!*/> typedArgs = HelperFuns.VarVector("arg", origIndexTypes, Gen);
      Contract.Assert(Cce.NonNullElements(typedArgs));
      List<VCExprVar /*!*/> indexes = HelperFuns.VarVector("x", indexTypes, Gen);
      Contract.Assert(Cce.NonNullElements(indexes));
      Contract.Assert(typedArgs.Count == indexes.Count);
      inParams.AddRange(typedArgs);
      quantifiedVars.AddRange(indexes);
      for (int i = 0; i < arity; i++)
      {
        bindings.VCExprVarBindings.Add(typedArgs[i], indexes[i]);
      }

      // bound variable:  val
      VCExprVar typedVal = Gen.Variable("val", mapResult);
      VCExprVar val = Gen.Variable("val", Cce.NonNull(select.OutParams[0]).TypedIdent.Type);
      quantifiedVars.Add(val);
      bindings.VCExprVarBindings.Add(typedVal, val);

      // add all type parameters into bindings
      foreach (TypeVariable tp in implicitTypeParamsSelect)
      {
        VCExprVar tVar = Gen.Variable(tp.Name, AxBuilderPremisses.T);
        bindings.TypeVariableBindings.Add(tp, tVar);
      }

      List<VCExpr /*!*/> typeParams = new List<VCExpr /*!*/>(explicitTypeParamsSelect.Count);
      foreach (TypeVariable tp in explicitTypeParamsSelect)
      {
        VCExprVar tVar = Gen.Variable(tp.Name, AxBuilderPremisses.T);
        bindings.TypeVariableBindings.Add(tp, tVar);
        // ... and record these explicit type-parameter arguments in typeParams
        typeParams.Add(tVar);
      }

      VCExpr /*!*/
        storeExpr = Store(store, m, indexes, val);
      Contract.Assert(storeExpr != null);
      VCExpr /*!*/
        selectExpr = Select(select, typeParams, storeExpr, indexes);
      Contract.Assert(selectExpr != null);

      // Create let-binding definitions for all type parameters.
      // The implicit ones can be phrased in terms of the types of the ordinary in-parameters, and
      // we want to make sure that they don't get phrased in terms of the out-parameter, so we pass
      // in inParams here.
      List<VCExprLetBinding /*!*/> letBindings_Implicit =
        AxBuilderPremisses.GenTypeParamBindings(implicitTypeParamsSelect, inParams, bindings, false);
      Contract.Assert(Cce.NonNullElements(letBindings_Implicit));
      // The explicit ones, by definition, can only be phrased in terms of the result, so we pass
      // in List(typedVal) here.
      List<VCExprLetBinding /*!*/> letBindings_Explicit =
        AxBuilderPremisses.GenTypeParamBindings(explicitTypeParamsSelect, HelperFuns.ToList(typedVal), bindings, false);
      Contract.Assert(Cce.NonNullElements(letBindings_Explicit));

      // generate:  select(store(m, indices, val)) == val
      VCExpr /*!*/
        eq = Gen.Eq(selectExpr, val);
      Contract.Assert(eq != null);
      // generate:  type(val) == T, where T is the type of val
      VCExpr /*!*/
        ante = Gen.Eq(
          AxBuilderPremisses.TypeOf(val),
          AxBuilderPremisses.Type2Term(mapResult, bindings.TypeVariableBindings));
      Contract.Assert(ante != null);
      VCExpr body;
      if (!AxBuilder.U.Equals(Cce.NonNull(select.OutParams[0]).TypedIdent.Type))
      {
        body = Gen.Let(letBindings_Explicit, eq);
      }
      else
      {
        body = Gen.Let(letBindings_Implicit, Gen.Let(letBindings_Explicit, Gen.ImpliesSimp(ante, eq)));
      }

      return Gen.Forall(quantifiedVars, new List<VCTrigger /*!*/>(), "mapAx0:" + select.Name, 0, body);
    }

    private VCExpr GenMapAxiom1(Function select, Function store, Type mapResult,
      List<TypeVariable /*!*/> /*!*/ explicitSelectParams)
    {
      Contract.Requires(mapResult != null);
      Contract.Requires(store != null);
      Contract.Requires(select != null);
      Contract.Requires(Cce.NonNullElements(explicitSelectParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      int arity = store.InParams.Count - 2;

      List<Type /*!*/> indexTypes = new List<Type /*!*/>();
      for (int i = 1; i < store.InParams.Count - 1; i++)
      {
        indexTypes.Add(Cce.NonNull(store.InParams[i]).TypedIdent.Type);
      }

      Contract.Assert(indexTypes.Count == arity);

      List<VCExprVar /*!*/> /*!*/
        indexes0 = HelperFuns.VarVector("x", indexTypes, Gen);
      Contract.Assert(Cce.NonNullElements(indexes0));
      List<VCExprVar /*!*/> /*!*/
        indexes1 = HelperFuns.VarVector("y", indexTypes, Gen);
      Contract.Assert(Cce.NonNullElements(indexes1));
      VCExprVar /*!*/
        m = Gen.Variable("m", AxBuilder.U);
      Contract.Assert(m != null);
      VCExprVar /*!*/
        val = Gen.Variable("val", Cce.NonNull(select.OutParams[0]).TypedIdent.Type);
      Contract.Assert(val != null);

      // extract the explicit type parameters from the actual result type ...
      VCExprVar /*!*/
        typedVal = Gen.Variable("val", mapResult);
      Contract.Assert(typedVal != null);
      VariableBindings /*!*/
        bindings = new VariableBindings();
      bindings.VCExprVarBindings.Add(typedVal, val);

      List<VCExprLetBinding /*!*/> /*!*/
        letBindings =
          AxBuilderPremisses.GenTypeParamBindings(explicitSelectParams,
            HelperFuns.ToList(typedVal),
            bindings, true);
      Contract.Assert(Cce.NonNullElements(letBindings));

      // ... and quantify the introduced term variables for type
      // parameters universally
      List<VCExprVar /*!*/> /*!*/
        typeParams = new List<VCExprVar /*!*/>(explicitSelectParams.Count);
      List<VCExpr /*!*/> /*!*/
        typeParamsExpr = new List<VCExpr /*!*/>(explicitSelectParams.Count);
      foreach (TypeVariable /*!*/ var in explicitSelectParams)
      {
        Contract.Assert(var != null);
        VCExprVar /*!*/
          newVar = (VCExprVar) bindings.TypeVariableBindings[var];
        Contract.Assert(newVar != null);
        typeParams.Add(newVar);
        typeParamsExpr.Add(newVar);
      }

      VCExpr /*!*/
        storeExpr = Store(store, m, indexes0, val);
      Contract.Assert(storeExpr != null);
      VCExpr /*!*/
        selectWithoutStoreExpr = Select(select, typeParamsExpr, m, indexes1);
      Contract.Assert(selectWithoutStoreExpr != null);
      VCExpr /*!*/
        selectExpr = Select(select, typeParamsExpr, storeExpr, indexes1);
      Contract.Assert(selectExpr != null);

      VCExpr /*!*/
        selectEq = Gen.Eq(selectExpr, selectWithoutStoreExpr);
      Contract.Assert(selectEq != null);

      List<VCExprVar /*!*/> /*!*/
        quantifiedVars = new List<VCExprVar /*!*/>(indexes0.Count + indexes1.Count + 2);
      quantifiedVars.Add(val);
      quantifiedVars.Add(m);
      quantifiedVars.AddRange(indexes0);
      quantifiedVars.AddRange(indexes1);
      quantifiedVars.AddRange(typeParams);

      List<VCTrigger /*!*/> /*!*/
        triggers = new List<VCTrigger /*!*/>();
      Contract.Assert(Cce.NonNullElements(triggers));

      VCExpr /*!*/
        axiom = VCExpressionGenerator.True;
      Contract.Assert(axiom != null);

      // first non-interference criterium: the queried location is
      // different from the assigned location
      for (int i = 0; i < arity; ++i)
      {
        VCExpr /*!*/
          indexesEq = Gen.Eq(indexes0[i], indexes1[i]);
        VCExpr /*!*/
          matrix = Gen.Or(indexesEq, selectEq);
        VCExpr /*!*/
          conjunct = Gen.Forall(quantifiedVars, triggers, "mapAx1:" + select.Name + ":" + i, 0, matrix);
        Contract.Assert(indexesEq != null);
        Contract.Assert(matrix != null);
        Contract.Assert(conjunct != null);
        axiom = Gen.AndSimp(axiom, conjunct);
      }

      // second non-interference criterion: the queried type is
      // different from the assigned type
      VCExpr /*!*/
        typesEq = VCExpressionGenerator.True;
      foreach (VCExprLetBinding /*!*/ b in letBindings)
      {
        Contract.Assert(b != null);
        typesEq = Gen.AndSimp(typesEq, Gen.Eq(b.V, b.E));
      }

      VCExpr /*!*/
        matrix2 = Gen.Or(typesEq, selectEq);
      VCExpr /*!*/
        conjunct2 = Gen.Forall(quantifiedVars, triggers, "mapAx2:" + select.Name, 0, matrix2);
      axiom = Gen.AndSimp(axiom, conjunct2);

      return axiom;
    }
  }

  /////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////
}