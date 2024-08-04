using System;
using System.Diagnostics;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  //=====================================================================
  //---------------------------------------------------------------------
  // Types
  [ContractClass(typeof(TypeContracts))]
  public abstract class Type : Absy
  {
    public Type(IToken /*!*/ token)
      : base(token)
    {
      Contract.Requires(token != null);
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively. Applying Clone to a type will return
    // a type in which all bound variables have been replaced with new
    // variables, whereas free variables have not changed

    public override Absy Clone()
    {
      Contract.Ensures(Contract.Result<Absy>() != null);
      return this.Clone(new Dictionary<TypeVariable /*!*/, TypeVariable /*!*/>());
    }

    public abstract Type /*!*/ Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap);

    /// <summary>
    /// Clones the type, but only syntactically.  Anything resolved in the source
    /// type is left unresolved (that is, with just the name) in the destination type.
    /// </summary>
    public abstract Type /*!*/ CloneUnresolved();

    //-----------  Linearisation  ----------------------------------

    public void Emit(TokenTextWriter stream)
    {
      Contract.Requires(stream != null);
      this.Emit(stream, 0);
    }

    public abstract void Emit(TokenTextWriter /*!*/ stream, int contextBindingStrength);

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      System.IO.StringWriter buffer = new System.IO.StringWriter();
      using TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false,  false, PrintOptions.Default);
      this.Emit(stream);

      return buffer.ToString();
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (ReferenceEquals(this, that))
      {
        return true;
      }

      Type thatType = that as Type;
      return thatType != null && this.Equals(thatType,
        new List<TypeVariable>(),
        new List<TypeVariable>());
    }

    [Pure]
    public abstract bool Equals(Type /*!*/ that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables);

    // used to skip leading type annotations (subexpressions of the
    // resulting type might still contain annotations)
    internal virtual Type /*!*/ Expanded
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return this;
      }
    }

    //-----------  Unification of types  -----------

    /// <summary>
    /// Add a constraint that this==that, if possible, and return true.
    /// If not possible, return false (which may have added some partial constraints).
    /// No error is printed.
    /// </summary>
    public bool Unify(Type that)
    {
      Contract.Requires(that != null);
      return Unify(that, new List<TypeVariable>(), new Dictionary<TypeVariable /*!*/, Type /*!*/>());
    }

    public abstract bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      // an idempotent substitution that describes the
      // unification result up to a certain point
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ unifier);

    [Pure]
    public static bool IsIdempotent(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ unifier)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(unifier));
      return unifier.Values.All(val => val.FreeVariables.All(var => !unifier.ContainsKey(var)));
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public abstract Type /*!*/ Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst);

    //-----------  Hashcodes  ----------------------------------

    // Hack to be able to access the hashcode of superclasses further up
    // (from the subclasses of this class)
    [Pure]
    protected int GetBaseHashCode()
    {
      return base.GetHashCode();
    }

    [Pure]
    public override int GetHashCode()
    {
      return this.GetHashCode(new List<TypeVariable>());
    }

    [Pure]
    public abstract int GetHashCode(List<TypeVariable> /*!*/ boundVariables);

    //-----------  Resolution  ----------------------------------

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      System.Diagnostics.Debug.Fail("Type.Resolve should never be called." +
                                    " Use Type.ResolveType instead");
    }

    public abstract Type /*!*/ ResolveType(ResolutionContext /*!*/ rc);

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      System.Diagnostics.Debug.Fail("Type.Typecheck should never be called");
    }

    // determine the free variables in a type, in the order in which the variables occur
    public abstract List<TypeVariable> /*!*/ FreeVariables { get; }

    // determine the free type proxies in a type, in the order in which they occur
    public abstract List<TypeProxy /*!*/> /*!*/ FreeProxies { get; }

    protected static void AppendWithoutDups<A>(List<A> a, List<A> b)
    {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      foreach (A x in b)
      {
        if (!a.Contains(x))
        {
          a.Add(x);
        }
      }
    }

    public bool IsClosed
    {
      get { return FreeVariables.Count == 0; }
    }

    //-----------  Getters/Issers  ----------------------------------

    // the following methods should be used instead of simple casts or the
    // C# "is" operator, because they handle type synonym annotations and
    // type proxies correctly

    public virtual bool IsBasic
    {
      get { return false; }
    }

    public virtual bool IsInt
    {
      get { return false; }
    }

    public virtual bool IsReal
    {
      get { return false; }
    }

    public virtual bool IsFloat
    {
      get { return false; }
    }

    public virtual bool IsBool
    {
      get { return false; }
    }

    public virtual bool IsRMode
    {
      get { return false; }
    }

    public virtual bool IsString
    {
      get { return false; }
    }

    public virtual bool IsRegEx
    {
      get { return false; }
    }

    public virtual bool IsSeq
    {
      get { return false; }
    }
    
    public virtual bool IsVariable
    {
      get { return false; }
    }

    public virtual TypeVariable /*!*/ AsVariable
    {
      get
      {
        Contract.Ensures(Contract.Result<TypeVariable>() != null);

        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.AsVariable should never be called
      }
    }

    public virtual bool IsCtor
    {
      get { return false; }
    }

    public virtual CtorType /*!*/ AsCtor
    {
      get
      {
        Contract.Ensures(Contract.Result<CtorType>() != null);

        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.AsCtor should never be called
      }
    }

    public virtual bool IsMap
    {
      get { return false; }
    }

    public virtual MapType /*!*/ AsMap
    {
      get
      {
        Contract.Ensures(Contract.Result<MapType>() != null);

        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.AsMap should never be called
      }
    }

    public virtual int MapArity
    {
      get
      {
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.MapArity should never be called
      }
    }

    public virtual bool IsUnresolved
    {
      get { return false; }
    }

    public virtual UnresolvedTypeIdentifier /*!*/ AsUnresolved
    {
      get
      {
        Contract.Ensures(Contract.Result<UnresolvedTypeIdentifier>() != null);

        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.AsUnresolved should never be called
      }
    }

    public virtual bool isFloat
    {
      get { return false; }
    }

    public virtual int FloatExponent
    {
      get
      {
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.FloatExponent should never be called
      }
    }

    public virtual int FloatSignificand
    {
      get
      {
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.FloatSignificand should never be called
      }
    }

    public virtual bool IsBv
    {
      get { return false; }
    }

    public virtual int BvBits
    {
      get
      {
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        } // Type.BvBits should never be called
      }
    }

    public static readonly Type /*!*/
      Int = new BasicType(SimpleType.Int);

    public static readonly Type /*!*/
      Real = new BasicType(SimpleType.Real);

    public static readonly Type /*!*/
      Bool = new BasicType(SimpleType.Bool);

    public static readonly Type /*!*/
      RMode = new BasicType(SimpleType.RMode);

    public static readonly Type /*!*/
      String = new BasicType(SimpleType.String);

    public static readonly Type /*!*/
      RegEx = new BasicType(SimpleType.RegEx);

    private static BvType[] bvtypeCache;

    static public BvType GetBvType(int sz)
    {
      Contract.Requires(0 <= sz);
      Contract.Ensures(Contract.Result<BvType>() != null);

      if (bvtypeCache == null)
      {
        bvtypeCache = new BvType[128];
      }

      if (sz < bvtypeCache.Length)
      {
        BvType t = bvtypeCache[sz];
        if (t == null)
        {
          t = new BvType(sz);
          bvtypeCache[sz] = t;
        }

        return t;
      }
      else
      {
        return new BvType(sz);
      }
    }

    static public FloatType GetFloatType(int sig, int exp)
    {
      Contract.Requires(0 <= exp);
      Contract.Requires(0 <= sig);
      Contract.Ensures(Contract.Result<FloatType>() != null);

      return new FloatType(sig, exp);
    }

    //------------ Match formal argument types on actual argument types
    //------------ and return the resulting substitution of type variables

    public static IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
      MatchArgumentTypes(List<TypeVariable> /*!*/ typeParams,
        List<Type> /*!*/ formalArgs,
        IList<Expr> /*!*/ actualArgs,
        List<Type> formalOuts,
        List<IdentifierExpr> actualOuts,
        string /*!*/ opName,
        TypecheckingContext /*!*/ tc)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(formalArgs != null);
      Contract.Requires(actualArgs != null);
      Contract.Requires(opName != null);
      Contract.Requires(tc != null);
      Contract.Requires(formalArgs.Count == actualArgs.Count);
      Contract.Requires((formalOuts == null) == (actualOuts == null));
      Contract.Requires(formalOuts == null || formalOuts.Count == Cce.NonNull(actualOuts).Count);
      Contract.Requires(tc == null || opName != null); //Redundant
      Contract.Ensures(Cce.NonNullDictionaryAndValues(Contract.Result<IDictionary<TypeVariable, Type>>()));

      // requires "actualArgs" and "actualOuts" to have been type checked

      Dictionary<TypeVariable /*!*/, Type /*!*/> subst = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      foreach (TypeVariable /*!*/ tv in typeParams)
      {
        Contract.Assert(tv != null);
        TypeProxy proxy = new TypeProxy(Token.NoToken, tv.Name);
        subst.Add(tv, proxy);
      }

      for (int i = 0; i < formalArgs.Count; i++)
      {
        Type formal = formalArgs[i].Substitute(subst);
        Type actual = Cce.NonNull(Cce.NonNull(actualArgs[i]).Type);
        // if the type variables to be matched occur in the actual
        // argument types, something has gone very wrong
        Contract.Assert(
          Contract.ForAll(0, typeParams.Count, index => !actual.FreeVariables.Contains(typeParams[index])));

        if (!formal.Unify(actual))
        {
          Contract.Assume(tc != null); // caller expected no errors
          Contract.Assert(opName != null); // follows from precondition
          tc.Error(Cce.NonNull(actualArgs[i]),
            "invalid type for argument {0} in {1}: {2} (expected: {3})",
            i, opName, actual, formalArgs[i]);
        }
      }

      if (formalOuts != null)
      {
        for (int i = 0; i < formalOuts.Count; ++i)
        {
          Type formal = formalOuts[i].Substitute(subst);
          Type actual = Cce.NonNull(Cce.NonNull(actualOuts)[i].Type);
          // if the type variables to be matched occur in the actual
          // argument types, something has gone very wrong
          Contract.Assert(Contract.ForAll(0, typeParams.Count, var => !actual.FreeVariables.Contains(typeParams[var])));

          if (!formal.Unify(actual))
          {
            Contract.Assume(tc != null); // caller expected no errors
            Contract.Assert(opName != null); // follows from precondition
            tc.Error(actualOuts[i],
              "invalid type for out-parameter {0} in {1}: {2} (expected: {3})",
              i, opName, actual, formal);
          }
        }
      }

      return subst;
    }

    //------------  Match formal argument types of a function or map
    //------------  on concrete types, substitute the result into the
    //------------  result type. Null is returned for type errors

    public static List<Type> CheckArgumentTypes(List<TypeVariable> /*!*/ typeParams,
        out List<Type /*!*/> /*!*/ actualTypeParams,
        List<Type> /*!*/ formalIns,
        IList<Expr> /*!*/ actualIns,
        List<Type> /*!*/ formalOuts,
        List<IdentifierExpr> actualOuts,
        IToken /*!*/ typeCheckingSubject,
        string /*!*/ opName,
        TypecheckingContext /*!*/ tc)
      // requires "actualIns" and "actualOuts" to have been type checked
    {
      Contract.Requires(typeParams != null);

      Contract.Requires(formalIns != null);
      Contract.Requires(formalOuts != null);
      Contract.Requires(actualIns != null);
      Contract.Requires(typeCheckingSubject != null);
      Contract.Requires(opName != null);
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out actualTypeParams)));
      actualTypeParams = new List<Type /*!*/>();

      if (formalIns.Count != actualIns.Count)
      {
        tc.Error(typeCheckingSubject, "wrong number of arguments in {0}: {1}",
          opName, actualIns.Count);
        // if there are no type parameters, we can still return the result
        // type and hope that the type checking proceeds
        return typeParams.Count == 0 ? formalOuts : null;
      }
      else if (actualOuts != null && formalOuts.Count != actualOuts.Count)
      {
        tc.Error(typeCheckingSubject, "wrong number of result variables in {0}: {1}",
          opName, actualOuts.Count);
        // if there are no type parameters, we can still return the result
        // type and hope that the type checking proceeds
        actualTypeParams = new List<Type>();
        return typeParams.Count == 0 ? formalOuts : null;
      }

      int previousErrorCount = tc.ErrorCount;
      IDictionary<TypeVariable /*!*/, Type /*!*/> subst =
        MatchArgumentTypes(typeParams, formalIns, actualIns,
          actualOuts != null ? formalOuts : null, actualOuts, opName, tc);
      Contract.Assert(Cce.NonNullDictionaryAndValues(subst));
      foreach (TypeVariable /*!*/ var in typeParams)
      {
        Contract.Assert(var != null);
        actualTypeParams.Add(subst[var]);
      }

      List<Type> /*!*/
        actualResults = new List<Type>();
      foreach (Type /*!*/ t in formalOuts)
      {
        Contract.Assert(t != null);
        actualResults.Add(t.Substitute(subst));
      }

      List<TypeVariable> resultFreeVars = FreeVariablesIn(actualResults);
      if (previousErrorCount != tc.ErrorCount)
      {
        // errors occured when matching the formal arguments
        // in case we have been able to substitute all type parameters,
        // we can still return the result type and hope that the
        // type checking proceeds in a meaningful manner
        if (typeParams.All(param => !resultFreeVars.Contains(param)))
        {
          return actualResults;
        }
        else
        {
          // otherwise there is no point in returning the result type,
          // type checking would only get confused even further
          return null;
        }
      }

      Contract.Assert(Contract.ForAll(0, typeParams.Count, index => !resultFreeVars.Contains(typeParams[index])));
      return actualResults;
    }

    ///////////////////////////////////////////////////////////////////////////

    // about the same as Type.CheckArgumentTypes, but without
    // detailed error reports
    public static Type /*!*/ InferValueType(List<TypeVariable> /*!*/ typeParams,
      List<Type> /*!*/ formalArgs,
      Type /*!*/ formalResult,
      List<Type> /*!*/ actualArgs)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(formalArgs != null);
      Contract.Requires(formalResult != null);
      Contract.Requires(actualArgs != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst =
          InferTypeParameters(typeParams, formalArgs, actualArgs);
      Contract.Assert(Cce.NonNullDictionaryAndValues(subst));

      Type /*!*/
        res = formalResult.Substitute(subst);
      Contract.Assert(res != null);
      // all type parameters have to be substituted with concrete types
      List<TypeVariable> /*!*/
        resFreeVars = res.FreeVariables;
      Contract.Assert(resFreeVars != null);
      Contract.Assert(Contract.ForAll(0, typeParams.Count, var => !resFreeVars.Contains(typeParams[var])));
      return res;
    }

    /// <summary>
    /// like Type.CheckArgumentTypes, but assumes no errors
    /// (and only does arguments, not results; and takes actuals as List<Type>, not List<Expr>)
    /// </summary>
    public static IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
      InferTypeParameters(List<TypeVariable> /*!*/ typeParams,
        List<Type> /*!*/ formalArgs,
        List<Type> /*!*/ actualArgs)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(formalArgs != null);
      Contract.Requires(actualArgs != null);
      Contract.Requires(formalArgs.Count == actualArgs.Count);
      Contract.Ensures(Cce.NonNullDictionaryAndValues(Contract.Result<IDictionary<TypeVariable, Type>>()));


      List<Type> proxies = new List<Type>();
      Dictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      foreach (TypeVariable /*!*/ tv in typeParams)
      {
        Contract.Assert(tv != null);
        TypeProxy proxy = new TypeProxy(Token.NoToken, tv.Name);
        proxies.Add(proxy);
        subst.Add(tv, proxy);
      }

      for (int i = 0; i < formalArgs.Count; i++)
      {
        Type formal = formalArgs[i].Substitute(subst);
        Type actual = actualArgs[i];
        // if the type variables to be matched occur in the actual
        // argument types, something has gone very wrong
        Contract.Assert(
          Contract.ForAll(0, typeParams.Count, index => !actual.FreeVariables.Contains(typeParams[index])));

        if (!formal.Unify(actual))
        {
          Contract.Assume(false); // caller expected no errors
        }
      }

      return subst;
    }

    //-----------  Helper methods to deal with bound type variables  ---------------

    public static void EmitOptionalTypeParams(TokenTextWriter stream, List<TypeVariable> typeParams)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(stream != null);
      if (typeParams.Count > 0)
      {
        stream.Write("<");
        typeParams.Emit(stream, ","); // default binding strength of 0 is ok
        stream.Write(">");
      }
    }

    // Sort the type parameters according to the order of occurrence in the argument types
    public static List<TypeVariable> /*!*/ SortTypeParams(List<TypeVariable> /*!*/ typeParams,
      List<Type> /*!*/ argumentTypes, Type resultType)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(argumentTypes != null);
      Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

      Contract.Ensures(Contract.Result<List<TypeVariable>>().Count == typeParams.Count);
      if (typeParams.Count == 0)
      {
        return typeParams;
      }

      List<TypeVariable> freeVarsInUse = FreeVariablesIn(argumentTypes);
      if (resultType != null)
      {
        freeVarsInUse.AppendWithoutDups(resultType.FreeVariables);
      }

      // "freeVarsInUse" is already sorted, but it may contain type variables not in "typeParams".
      // So, project "freeVarsInUse" onto "typeParams":
      List<TypeVariable> sortedTypeParams = new List<TypeVariable>();
      foreach (TypeVariable /*!*/ var in freeVarsInUse)
      {
        Contract.Assert(var != null);
        if (typeParams.Contains(var))
        {
          sortedTypeParams.Add(var);
        }
      }

      if (sortedTypeParams.Count < typeParams.Count)
      {
        // add the type parameters not mentioned in "argumentTypes" in
        // the end of the list (this can happen for quantifiers)
        sortedTypeParams.AppendWithoutDups(typeParams);
      }

      return sortedTypeParams;
    }

    // Check that each of the type parameters occurs in at least one argument type.
    // Return true if some type parameters appear only among "moreArgumentTypes" and
    // not in "argumentTypes".
    [Pure]
    public static void CheckBoundVariableOccurrences(List<TypeVariable> /*!*/ typeParams,
      List<Type> /*!*/ argumentTypes,
      List<Type> moreArgumentTypes,
      IToken /*!*/ resolutionSubject,
      string /*!*/ subjectName,
      ResolutionContext /*!*/ rc)
    {
      Contract.Requires(typeParams != null);
      Contract.Requires(argumentTypes != null);
      Contract.Requires(resolutionSubject != null);
      Contract.Requires(subjectName != null);
      Contract.Requires(rc != null);
      List<TypeVariable> freeVarsInArgs = FreeVariablesIn(argumentTypes);
      List<TypeVariable> moreFreeVarsInArgs = moreArgumentTypes == null ? new List<TypeVariable>() : FreeVariablesIn(moreArgumentTypes);
      foreach (TypeVariable /*!*/ var in typeParams)
      {
        Contract.Assert(var != null);
        if (rc.LookUpTypeBinder(var.Name) == var) // avoid to complain twice about variables that are bound multiple times
        {
          if (freeVarsInArgs.Contains(var))
          {
            // ok
          }
          else if (moreFreeVarsInArgs.Contains(var))
          {
            // ok
          }
          else
          {
            rc.Error(resolutionSubject,
              "type variable must occur in {0}: {1}",
              subjectName, var);
          }
        }
      }
    }

    [Pure]
    public static List<TypeVariable> FreeVariablesIn(List<Type> arguments)
    {
      Contract.Requires(arguments != null);
      Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);
      List<TypeVariable> /*!*/
        res = new List<TypeVariable>();
      foreach (Type /*!*/ t in arguments)
      {
        Contract.Assert(t != null);
        res.AppendWithoutDups(t.FreeVariables);
      }

      return res;
    }
  }

  [ContractClassFor(typeof(Type))]
  public abstract class TypeContracts : Type
  {
    public TypeContracts() : base(null)
    {
    }

    public override List<TypeProxy> FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        throw new NotImplementedException();
      }
    }

    public override List<TypeVariable> FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);
        throw new NotImplementedException();
      }
    }

    public override Type Clone(IDictionary<TypeVariable, TypeVariable> varMap)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }

    public override bool Equals(Type that, List<TypeVariable> thisBoundVariables, List<TypeVariable> thatBoundVariables)
    {
      Contract.Requires(that != null);
      Contract.Requires(thisBoundVariables != null);
      Contract.Requires(thatBoundVariables != null);
      throw new NotImplementedException();
    }

    public override bool Unify(Type that, List<TypeVariable> unifiableVariables,
      IDictionary<TypeVariable, Type> unifier)
    {
      Contract.Requires(that != null);
      Contract.Requires(unifiableVariables != null);
      Contract.Requires(Cce.NonNullDictionaryAndValues(unifier));
      Contract.Requires(Contract.ForAll(unifier.Keys, key => unifiableVariables.Contains(key)));
      Contract.Requires(IsIdempotent(unifier));
      throw new NotImplementedException();
    }

    public override Type Substitute(IDictionary<TypeVariable, Type> subst)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(subst));
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public override Type ResolveType(ResolutionContext rc)
    {
      Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      Contract.Requires(boundVariables != null);
      throw new NotImplementedException();
    }
  }
  //=====================================================================

  public class BasicType : Type
  {
    public readonly SimpleType T;

    public BasicType(IToken /*!*/ token, SimpleType t)
      : base(token)
    {
      Contract.Requires(token != null);
      T = t;
    }

    public BasicType(SimpleType t)
      : base(Token.NoToken)
    {
      T = t;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively.

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      // BasicTypes are immutable anyway, we do not clone
      return this;
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      // no parentheses are necessary for basic types
      stream.SetToken(this);
      stream.Write("{0}", this);
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      switch (T)
      {
        case SimpleType.Int:
          return "int";
        case SimpleType.Real:
          return "real";
        case SimpleType.Bool:
          return "bool";
        case SimpleType.RMode:
          return "rmode";
        case SimpleType.String:
          return "string";
        case SimpleType.RegEx:
          return "regex";
      }

      Debug.Assert(false, "bad type " + T);
      {
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      } // make compiler happy
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      // shortcut
      Type thatType = that as Type;
      if (thatType == null)
      {
        return false;
      }

      BasicType thatBasicType = TypeProxy.FollowProxy(thatType.Expanded) as BasicType;
      return thatBasicType != null && this.T == thatBasicType.T;
    }

    [Pure]
    public override bool Equals(Type that, List<TypeVariable> thisBoundVariables, List<TypeVariable> thatBoundVariables)
    {
      //Contract.Requires(thatBoundVariables != null);
      //Contract.Requires(thisBoundVariables != null);
      //Contract.Requires(that != null);
      return this.Equals(that);
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type that, List<TypeVariable> unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ unifier)
    {
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(that != null);
      //Contract.Requires(cce.NonNullElements(unifier));
      // an idempotent substitution that describes the
      // unification result up to a certain point

      that = that.Expanded;
      if (that is TypeProxy || that is TypeVariable)
      {
        return that.Unify(this, unifiableVariables, unifier);
      }
      else
      {
        return this.Equals(that);
      }
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      return this.T.GetHashCode();
    }

    [Pure]
    public override int GetHashCode()
    {
      return this.T.GetHashCode();
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // nothing to resolve
      return this;
    }

    // determine the free variables in a type, in the order in which the variables occur
    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

        return new List<TypeVariable>(); // basic type are closed
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        return new List<TypeProxy /*!*/>();
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsBasic
    {
      get { return true; }
    }

    public override bool IsInt
    {
      get { return this.T == SimpleType.Int; }
    }

    public override bool IsReal
    {
      get { return this.T == SimpleType.Real; }
    }

    public override bool IsBool
    {
      get { return this.T == SimpleType.Bool; }
    }

    public override bool IsRMode
    {
      get { return this.T == SimpleType.RMode; }
    }

    public override bool IsString
    {
      get { return this.T == SimpleType.String; }
    }

    public override bool IsRegEx
    {
      get { return this.T == SimpleType.RegEx; }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBasicType(this);
    }
  }

  //=====================================================================

  //Note that the functions in this class were directly copied from the BV class just below
  public class FloatType : Type
  {
    public readonly int Significand; //Size of Significand in bits
    public readonly int Exponent; //Size of exponent in bits

    public FloatType(IToken token, int significand, int exponent)
      : base(token)
    {
      Contract.Requires(token != null);
      Significand = significand;
      Exponent = exponent;
    }

    public FloatType(int significand, int exponent)
      : base(Token.NoToken)
    {
      Significand = significand;
      Exponent = exponent;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively.

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      // FloatTypes are immutable anyway, we do not clone
      return this;
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      // no parentheses are necessary for bitvector-types
      stream.SetToken(this);
      stream.Write("{0}", this);
    }

    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return "float" + Significand + "e" + Exponent;
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type /*!*/ that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      FloatType thatFloatType = TypeProxy.FollowProxy(that.Expanded) as FloatType;
      return thatFloatType != null && this.Significand == thatFloatType.Significand &&
             this.Exponent == thatFloatType.Exponent;
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      // an idempotent substitution that describes the
      // unification result up to a certain point
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ unifier)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(cce.NonNullElements(unifier));
      that = that.Expanded;
      if (that is TypeProxy || that is TypeVariable)
      {
        return that.Unify(this, unifiableVariables, unifier);
      }
      else
      {
        return this.Equals(that);
      }
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      return this.Significand.GetHashCode() + this.Exponent.GetHashCode();
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // nothing to resolve
      return this;
    }

    // determine the free variables in a type, in the order in which the variables occur
    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

        return new List<TypeVariable>(); // bitvector-type are closed
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        return new List<TypeProxy /*!*/>();
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsFloat
    {
      get { return true; }
    }

    public override int FloatSignificand
    {
      get { return Significand; }
    }

    public override int FloatExponent
    {
      get { return Exponent; }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitFloatType(this);
    }
  }

  //=====================================================================

  public class BvType : Type
  {
    public readonly int Bits;

    public BvType(IToken token, int bits)
      : base(token)
    {
      Contract.Requires(token != null);
      Bits = bits;
    }

    public BvType(int bits)
      : base(Token.NoToken)
    {
      Bits = bits;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively.

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      // BvTypes are immutable anyway, we do not clone
      return this;
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      // no parentheses are necessary for bitvector-types
      stream.SetToken(this);
      stream.Write("{0}", this);
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return "bv" + Bits;
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type /*!*/ that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      //Contract.Requires(thisBoundVariables != null);
      //Contract.Requires(thatBoundVariables != null);
      //Contract.Requires(that != null);
      BvType thatBvType = TypeProxy.FollowProxy(that.Expanded) as BvType;
      return thatBvType != null && this.Bits == thatBvType.Bits;
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      // an idempotent substitution that describes the
      // unification result up to a certain point
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ unifier)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(cce.NonNullElements(unifier));
      that = that.Expanded;
      if (that is TypeProxy || that is TypeVariable)
      {
        return that.Unify(this, unifiableVariables, unifier);
      }
      else
      {
        return this.Equals(that);
      }
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      return this.Bits.GetHashCode();
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // nothing to resolve
      return this;
    }

    // determine the free variables in a type, in the order in which the variables occur
    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

        return new List<TypeVariable>(); // bitvector-type are closed
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        return new List<TypeProxy /*!*/>();
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsBv
    {
      get { return true; }
    }

    public override int BvBits
    {
      get { return Bits; }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBvType(this);
    }
  }

  //=====================================================================

  // An AST node containing an identifier and a sequence of type arguments, which
  // will be turned either into a TypeVariable, into a CtorType or into a BvType
  // during the resolution phase
  public class UnresolvedTypeIdentifier : Type
  {
    public readonly string /*!*/
      Name;

    public readonly List<Type> /*!*/
      Arguments;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Name != null);
      Contract.Invariant(Arguments != null);
    }


    public UnresolvedTypeIdentifier(IToken token, string name)
      : this(token, name, new List<Type>())
    {
      Contract.Requires(name != null);
      Contract.Requires(token != null);
    }

    public UnresolvedTypeIdentifier(IToken token, string name, List<Type> arguments)
      : base(token)
    {
      Contract.Requires(arguments != null);
      Contract.Requires(name != null);
      Contract.Requires(token != null);
      this.Name = name;
      this.Arguments = arguments;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.Clone(varMap));
      }

      return new UnresolvedTypeIdentifier(tok, Name, newArgs);
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.CloneUnresolved());
      }

      return new UnresolvedTypeIdentifier(tok, Name, newArgs);
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      //Contract.Requires(thisBoundVariables != null);
      //Contract.Requires(thatBoundVariables != null);
      //Contract.Requires(that != null);
      System.Diagnostics.Debug.Fail("UnresolvedTypeIdentifier.Equals should never be called");
      return false; // to make the compiler happy      
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type that,
      List<TypeVariable> /*!*/ unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> result)
    {
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(cce.NonNullElements(result));
      //Contract.Requires(that != null);
      {
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      } // UnresolvedTypeIdentifier.Unify should never be called
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      {
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      } // UnresolvedTypeIdentifier.Substitute should never be called
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      {
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      } // UnresolvedTypeIdentifier.GetHashCode should never be called
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // first case: the type name denotes a bitvector-type, float-type, rmode-type, string-type, or regex-type

      if (Name.StartsWith("bv") && Name.Length > 2)
      {
        bool is_bv = true;
        for (int i = 2; i < Name.Length; ++i)
        {
          if (!char.IsDigit(Name[i]))
          {
            is_bv = false;
            break;
          }
        }

        if (is_bv)
        {
          if (Arguments.Count > 0)
          {
            rc.Error(this,
              "bitvector types must not be applied to arguments: {0}",
              Name);
          }

          return new BvType(tok, int.Parse(Name.Substring(2)));
        }
      }

      if (Name.StartsWith("float") && Name.Length > 5)
      {
        bool is_float = true;
        int i = 5;
        for (; is_float && Name[i] != 'e'; i++)
        {
          if (i >= Name.Length - 1 || !char.IsDigit(Name[i])) //There must be an e
          {
            is_float = false;
          }
        }

        int mid = i;
        i++;
        for (; i < Name.Length && is_float; i++)
        {
          if (!char.IsDigit(Name[i]))
          {
            is_float = false;
          }
        }

        if (is_float)
        {
          if (Arguments.Count > 0)
          {
            rc.Error(this,
              "float types must not be applied to arguments: {0}",
              Name);
          }

          return new FloatType(tok, int.Parse(Name.Substring(5, mid - 5)), int.Parse(Name.Substring(mid + 1)));
        }
      }

      if (Name.Equals("rmode"))
      {
        if (Arguments.Count > 0)
        {
          rc.Error(this,
            "rounding mode type must not be applied to arguments: {0}",
            Name);
        }

        return Type.RMode;
      }

      if (Name.Equals("string"))
      {
        if (Arguments.Count > 0)
        {
          rc.Error(this,
            "string type must not be applied to arguments: {0}",
            Name);
        }

        return Type.String;
      }

      if (Name.Equals("regex"))
      {
        if (Arguments.Count > 0)
        {
          rc.Error(this,
            "regex type must not be applied to arguments: {0}",
            Name);
        }

        return Type.RegEx;
      }

      // second case: the identifier is resolved to a type variable
      TypeVariable var = rc.LookUpTypeBinder(Name);
      if (var != null)
      {
        if (Arguments.Count > 0)
        {
          rc.Error(this,
            "type variables must not be applied to arguments: {0}",
            var);
        }

        return var;
      }

      // third case: the identifier denotes a type constructor and we
      // recursively resolve the arguments
      TypeCtorDecl ctorDecl = rc.LookUpType(Name);
      if (ctorDecl != null)
      {
        if (Arguments.Count != ctorDecl.Arity)
        {
          rc.Error(this,
            "type constructor received wrong number of arguments: {0}",
            ctorDecl);
          return this;
        }

        return new CtorType(tok, ctorDecl, ResolveArguments(rc));
      }

      // fourth case: the identifier denotes a type synonym
      TypeSynonymDecl synDecl = rc.LookUpTypeSynonym(Name);
      if (synDecl != null)
      {
        if (Arguments.Count != synDecl.TypeParameters.Count)
        {
          rc.Error(this,
            "type synonym received wrong number of arguments: {0}",
            synDecl);
          return this;
        }

        List<Type> /*!*/
          resolvedArgs = ResolveArguments(rc);
        Contract.Assert(resolvedArgs != null);

        return new TypeSynonymAnnotation(this.tok, synDecl, resolvedArgs);
      }

      // otherwise: this name is not declared anywhere
      rc.Error(this, "undeclared type: {0}", Name);
      return this;
    }

    private List<Type> ResolveArguments(ResolutionContext rc)
    {
      Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<List<Type>>() != null);
      List<Type> /*!*/
        resolvedArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        resolvedArgs.Add(t.ResolveType(rc));
      }

      return resolvedArgs;
    }

    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

        return new List<TypeVariable>();
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        return new List<TypeProxy /*!*/>();
      }
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      // PR: should unresolved types be syntactically distinguished from resolved types?
      CtorType.EmitCtorType(this.Name, Arguments, stream, contextBindingStrength);
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsUnresolved
    {
      get { return true; }
    }

    public override UnresolvedTypeIdentifier /*!*/ AsUnresolved
    {
      get
      {
        Contract.Ensures(Contract.Result<UnresolvedTypeIdentifier>() != null);
        return this;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitUnresolvedTypeIdentifier(this);
    }
  }

  //=====================================================================

  public class TypeVariable : Type
  {
    public readonly string /*!*/
      Name;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Name != null);
    }


    public TypeVariable(IToken token, string name)
      : base(token)
    {
      Contract.Requires(name != null);
      Contract.Requires(token != null);
      this.Name = name;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      // if this variable is mapped to some new variable, we take the new one
      // otherwise, return this
      varMap.TryGetValue(this, out var res);
      if (res == null)
      {
        return this;
      }
      else
      {
        return res;
      }
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return this;
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      //Contract.Requires(thisBoundVariables != null);
      //Contract.Requires(thatBoundVariables != null);
      //Contract.Requires(that != null);
      TypeVariable thatAsTypeVar = TypeProxy.FollowProxy(that.Expanded) as TypeVariable;

      if (thatAsTypeVar == null)
      {
        return false;
      }

      int thisIndex = thisBoundVariables.LastIndexOf(this);
      int thatIndex = thatBoundVariables.LastIndexOf(thatAsTypeVar);
      return (thisIndex >= 0 && thisIndex == thatIndex) ||
             (thisIndex == -1 && thatIndex == -1 &&
              Object.ReferenceEquals(this, thatAsTypeVar));
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      // an idempotent substitution that describes the
      // unification result up to a certain point
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ unifier)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(cce.NonNullElements(unifier));
      that = that.Expanded;
      if (that is TypeProxy && !(that is ConstrainedProxy))
      {
        return that.Unify(this, unifiableVariables, unifier);
      }

      if (this.Equals(that))
      {
        return true;
      }

      if (unifiableVariables.Contains(this))
      {
        unifier.TryGetValue(this, out var previousSubst);
        if (previousSubst == null)
        {
          return addSubstitution(unifier, that);
        }
        else
        {
          // we have to unify the old instantiation with the new one
          return previousSubst.Unify(that, unifiableVariables, unifier);
        }
      }

      // this cannot be instantiated with anything
      // but that possibly can ...

      TypeVariable tv = that as TypeVariable;

      return tv != null &&
             unifiableVariables.Contains(tv) &&
             that.Unify(this, unifiableVariables, unifier);
    }

    // TODO: the following might cause problems, because when applying substitutions
    // to type proxies the substitutions are not propagated to the proxy
    // constraints (right now at least)
    private bool addSubstitution(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ oldSolution,
      // the type that "this" is instantiated with
      Type /*!*/ newSubst)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(oldSolution));
      Contract.Requires(newSubst != null);
      Contract.Requires(!oldSolution.ContainsKey(this));

      Dictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        newMapping = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      // apply the old (idempotent) substitution to the new instantiation
      Type /*!*/
        substSubst = newSubst.Substitute(oldSolution);
      Contract.Assert(substSubst != null);
      // occurs check
      if (substSubst.FreeVariables.Contains(this))
      {
        return false;
      }

      newMapping.Add(this, substSubst);

      // apply the new substitution to the old ones to ensure idempotence
      List<TypeVariable /*!*/> /*!*/
        keys = new List<TypeVariable /*!*/>();
      keys.AddRange(oldSolution.Keys);
      foreach (TypeVariable /*!*/ var in keys)
      {
        Contract.Assert(var != null);
        oldSolution[var] = oldSolution[var].Substitute(newMapping);
      }

      oldSolution.Add(this, substSubst);

      Contract.Assert(IsIdempotent(oldSolution));
      return true;
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      if (subst.TryGetValue(this, out var res))
      {
        Contract.Assert(res != null);
        return res;
      }
      else
      {
        return this;
      }
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      int thisIndex = boundVariables.LastIndexOf(this);
      if (thisIndex == -1)
      {
        return GetBaseHashCode();
      }

      return thisIndex * 27473671;
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      // never put parentheses around variables
      stream.SetToken(this);
      stream.Write("{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      //Contract.Ensures(Contract.Result<Type>() != null);
      // nothing to resolve
      return this;
    }

    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);
        return new List<TypeVariable> {this};
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        return new List<TypeProxy /*!*/>();
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsVariable
    {
      get { return true; }
    }

    public override TypeVariable /*!*/ AsVariable
    {
      get
      {
        Contract.Ensures(Contract.Result<TypeVariable>() != null);
        return this;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      //Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTypeVariable(this);
    }
  }

  //=====================================================================

  public class TypeProxy : Type
  {
    static int proxies = 0;

    public readonly string /*!*/
      Name;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Name != null);
    }


    public TypeProxy(IToken token, string givenName)
      : this(token, givenName, "proxy")
    {
      Contract.Requires(givenName != null);
      Contract.Requires(token != null);
    }

    protected TypeProxy(IToken token, string givenName, string kind)
      : base(token)
    {
      Contract.Requires(kind != null);
      Contract.Requires(givenName != null);
      Contract.Requires(token != null);
      Name = givenName + "$" + kind + "#" + proxies;
      proxies++;
    }

    private Type proxyFor;

    public Type ProxyFor
    {
      // apply path shortening, and then return the value of proxyFor
      get
      {
        TypeProxy anotherProxy = proxyFor as TypeProxy;
        if (anotherProxy != null && anotherProxy.proxyFor != null)
        {
          // apply path shortening by bypassing "anotherProxy" (and possibly others)
          proxyFor = anotherProxy.ProxyFor;
          Contract.Assert(proxyFor != null);
        }

        return proxyFor;
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Everything)]
    public static Type FollowProxy(Type t)
    {
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Ensures(
        !(Contract.Result<Type>() is TypeProxy) || ((TypeProxy) Contract.Result<Type>()).proxyFor == null);
      if (t is TypeProxy)
      {
        Type p = ((TypeProxy) t).ProxyFor;
        if (p != null)
        {
          return p;
        }
      }

      return t;
    }

    protected void DefineProxy(Type ty)
    {
      Contract.Requires(ty != null);
      Contract.Requires(ProxyFor == null);
      // follow ty down to the leaf level, so that we can avoid creating a cycle
      ty = FollowProxy(ty);
      if (!object.ReferenceEquals(this, ty))
      {
        proxyFor = ty;
      }
    }

    //-----------  Cloning  ----------------------------------

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Clone(varMap);
      }
      else
      {
        return new TypeProxy(this.tok, this.Name); // the clone will have a name that ends with $proxy<n>$proxy<m>
      }
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return new TypeProxy(this.tok, this.Name); // the clone will have a name that ends with $proxy<n>$proxy<m>
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      //Contract.Requires(thisBoundVariables != null);
      //Contract.Requires(thatBoundVariables != null);
      //Contract.Requires(that != null);
      if (object.ReferenceEquals(this, that))
      {
        return true;
      }

      Type p = ProxyFor;
      if (p != null)
      {
        return p.Equals(that, thisBoundVariables, thatBoundVariables);
      }
      else
      {
        // This proxy could be made to be equal to anything, so what to return?
        return false;
      }
    }

    //-----------  Unification of types  -----------

    // determine whether the occurs check fails: this is a strict subtype of that
    protected bool ReallyOccursIn(Type that)
    {
      Contract.Requires(that != null);
      that = FollowProxy(that.Expanded);
      return that.FreeProxies.Contains(this) &&
             (that.IsCtor || that.IsMap && this != that && this.ProxyFor != that);
    }

    public override bool Unify(Type that,
      List<TypeVariable> /*!*/ unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> result)
    {
      //Contract.Requires(cce.NonNullElements(result));
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(that != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Unify(that, unifiableVariables, result);
      }
      else
      {
        // unify this with that
        if (this.ReallyOccursIn(that))
        {
          return false;
        }

        DefineProxy(that.Expanded);
        return true;
      }
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Substitute(subst);
      }
      else
      {
        return this;
      }
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.GetHashCode(boundVariables);
      }
      else
      {
        return GetBaseHashCode();
      }
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      Type p = ProxyFor;
      if (p != null)
      {
        p.Emit(stream, contextBindingStrength);
      }
      else
      {
        // no need for parentheses
        stream.SetToken(this);
        stream.Write("{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
      }
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.ResolveType(rc);
      }
      else
      {
        return this;
      }
    }

    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

        Type p = ProxyFor;
        if (p != null)
        {
          return p.FreeVariables;
        }
        else
        {
          return new List<TypeVariable>();
        }
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        Type p = ProxyFor;
        if (p != null)
        {
          return p.FreeProxies;
        }
        else
        {
          List<TypeProxy /*!*/> /*!*/
            res = new List<TypeProxy /*!*/>();
          res.Add(this);
          return res;
        }
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsBasic
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsBasic;
      }
    }

    public override bool IsInt
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsInt;
      }
    }

    public override bool IsReal
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsReal;
      }
    }

    public override bool IsFloat
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsFloat;
      }
    }

    public override int FloatExponent
    {
      get
      {
        Type p = ProxyFor;
        if (p == null || !p.IsFloat)
        {
          return base.FloatExponent; //Shouldn't happen, so get an unreachable exception
        }

        return p.FloatExponent;
      }
    }

    public override int FloatSignificand
    {
      get
      {
        Type p = ProxyFor;
        if (p == null || !p.IsFloat)
        {
          return base.FloatSignificand; //Shouldn't happen, so get an unreachable exception
        }

        return p.FloatSignificand;
      }
    }

    public override bool IsBool
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsBool;
      }
    }

    public override bool IsRMode
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsRMode;
      }
    }

    public override bool IsString
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsString;
      }
    }

    public override bool IsRegEx
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsRegEx;
      }
    }

    public override bool IsVariable
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsVariable;
      }
    }

    public override TypeVariable /*!*/ AsVariable
    {
      get
      {
        Contract.Ensures(Contract.Result<TypeVariable>() != null);

        Type p = ProxyFor;
        Contract.Assume(p != null);
        return p.AsVariable;
      }
    }

    public override bool IsCtor
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsCtor;
      }
    }

    public override CtorType /*!*/ AsCtor
    {
      get
      {
        Contract.Ensures(Contract.Result<CtorType>() != null);

        Type p = ProxyFor;
        Contract.Assume(p != null);
        return p.AsCtor;
      }
    }

    public override bool IsMap
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsMap;
      }
    }

    public override MapType /*!*/ AsMap
    {
      get
      {
        Contract.Ensures(Contract.Result<MapType>() != null);

        Type p = ProxyFor;
        Contract.Assume(p != null);
        return p.AsMap;
      }
    }

    public override int MapArity
    {
      get
      {
        Type p = ProxyFor;
        Contract.Assume(p != null);
        return p.MapArity;
      }
    }

    public override bool IsUnresolved
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsUnresolved;
      }
    }

    public override UnresolvedTypeIdentifier /*!*/ AsUnresolved
    {
      get
      {
        Contract.Ensures(Contract.Result<UnresolvedTypeIdentifier>() != null);

        Type p = ProxyFor;
        Contract.Assume(p != null);
        return p.AsUnresolved;
      }
    }

    public override bool IsBv
    {
      get
      {
        Type p = ProxyFor;
        return p != null && p.IsBv;
      }
    }

    public override int BvBits
    {
      get
      {
        Type p = ProxyFor;
        Contract.Assume(p != null);
        return p.BvBits;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTypeProxy(this);
    }
  }

  public abstract class ConstrainedProxy : TypeProxy
  {
    protected ConstrainedProxy(IToken token, string givenName, string kind)
      : base(token, givenName, kind)
    {
      Contract.Requires(kind != null);
      Contract.Requires(givenName != null);
      Contract.Requires(token != null);
    }
  }

  /// <summary>
  /// Each instance of this class represents a set of bitvector types.  In particular, it represents
  /// a bitvector type bvN iff
  ///   minBits ATMOST N  and
  ///   foreach constraint (t0,t1), the types represented by t0 and t1 are bitvector types whose
  ///   number of bits add up to N.
  /// This means that the size of a BvTypeProxy p is constrained not only by p.minBits, but also
  /// by the size of various t0 and t1 types that are transitively part of BvTypeProxy constraints.
  /// If such a t0 or t1 were to get its ProxyFor field defined, then p would have to be further
  /// constrained too.  This doesn't seem like it would ever occur in a Boogie program, because:
  ///   the only place where a BvTypeProxy with constraints can occur is as the type of a
  ///   BvConcatExpr, and
  ///   the types of all local variables are explicitly declared, which means that the types of
  ///   subexpressions of a BvConcatExpr are not going to change other than via the type of the
  ///   BvConcatExpr.
  /// So, this implementation of BvTypeProxy does not keep track of where a BvTypeProxy may occur
  /// transitively in some other BvTypeProxy's constraints.
  /// </summary>
  public class BvTypeProxy : ConstrainedProxy
  {
    public int MinBits;
    List<BvTypeConstraint /*!*/> constraints;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(constraints, true));
    }

    class BvTypeConstraint
    {
      public Type /*!*/
        T0;

      public Type /*!*/
        T1;

      public BvTypeConstraint(Type t0, Type t1)
      {
        Contract.Requires(t1 != null);
        Contract.Requires(t0 != null);
        Contract.Requires(t0.IsBv && t1.IsBv);
        T0 = t0;
        T1 = t1;
      }
    }

    public BvTypeProxy(IToken token, string name, int minBits)
      : base(token, name, "bv" + minBits + "proxy")
    {
      Contract.Requires(name != null);
      Contract.Requires(token != null);
      this.MinBits = minBits;
    }

    /// <summary>
    /// Requires that any further constraints to be placed on t0 and t1 go via the object to
    /// be constructed.
    /// </summary>
    public BvTypeProxy(IToken token, string name, Type t0, Type t1)
      : base(token, name, "bvproxy")
    {
      Contract.Requires(t1 != null);
      Contract.Requires(t0 != null);
      Contract.Requires(name != null);
      Contract.Requires(token != null);
      Contract.Requires(t0.IsBv && t1.IsBv);
      t0 = FollowProxy(t0);
      t1 = FollowProxy(t1);
      this.MinBits = MinBitsFor(t0) + MinBitsFor(t1);
      List<BvTypeConstraint /*!*/> list = new List<BvTypeConstraint /*!*/>();
      list.Add(new BvTypeConstraint(t0, t1));
      this.constraints = list;
    }

    /// <summary>
    /// Construct a BvTypeProxy like p, but with minBits.
    /// </summary>
    private BvTypeProxy(BvTypeProxy p, int minBits)
      : base(p.tok, p.Name, "")
    {
      Contract.Requires(p != null);
      this.MinBits = minBits;
      this.constraints = p.constraints;
    }

    private BvTypeProxy(IToken token, string name, int minBits, List<BvTypeConstraint /*!*/> constraints)
      : base(token, name, "")
    {
      Contract.Requires(Cce.NonNullElements(constraints, true));
      Contract.Requires(name != null);
      Contract.Requires(token != null);
      this.MinBits = minBits;
      this.constraints = constraints;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Everything)]
    private static int MinBitsFor(Type t)
    {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBv);
      Contract.Ensures(0 <= Contract.Result<int>());

      if (t is TypeSynonymAnnotation)
      {
        return MinBitsFor(((TypeSynonymAnnotation) t).ExpandedType);
      }

      if (t is BvType)
      {
        return t.BvBits;
      }
      else
      {
        return ((BvTypeProxy) t).MinBits;
      }
    }

    //-----------  Cloning  ----------------------------------

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Clone(varMap);
      }
      else
      {
        return new BvTypeProxy(this.tok, this.Name, this.MinBits,
          this.constraints); // the clone will have a name that ends with $bvproxy<n>$bvproxy<m>
      }
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      return new BvTypeProxy(this.tok, this.Name, this.MinBits,
        this.constraints); // the clone will have a name that ends with $bvproxy<n>$bvproxy<m>
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type that,
      List<TypeVariable> unifiableVariables,
      IDictionary<TypeVariable, Type> result)
    {
      //Contract.Requires(cce.NonNullElements(result));
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(that != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Unify(that, unifiableVariables, result);
      }

      // unify this with that, if possible
      that = that.Expanded;
      that = FollowProxy(that);

      if (this.ReallyOccursIn(that))
      {
        return false;
      }

      TypeVariable tv = that as TypeVariable;

      if (tv != null && unifiableVariables.Contains(tv))
      {
        return that.Unify(this, unifiableVariables, result);
      }

      if (object.ReferenceEquals(this, that))
      {
        return true;
      }
      else if (that is BvType)
      {
        if (MinBits <= that.BvBits)
        {
          if (constraints != null)
          {
            foreach (BvTypeConstraint btc in constraints)
            {
              int minT1 = MinBitsFor(btc.T1);
              int left = IncreaseBits(btc.T0, that.BvBits - minT1);
              left = IncreaseBits(btc.T1, minT1 + left);
              Contract.Assert(
                left == 0); // because it should always be possible to increase the total size of a BvTypeConstraint pair (t0,t1) arbitrarily
            }
          }

          DefineProxy(that);
          return true;
        }
      }
      else if (that is BvTypeProxy)
      {
        BvTypeProxy bt = (BvTypeProxy) that;
        // keep the proxy with the stronger constraint (that is, the higher minBits), but if either
        // has a constraints list, then concatenate both constraints lists and define the previous
        // proxies to the new one
        if (this.constraints != null || bt.constraints != null)
        {
          List<BvTypeConstraint /*!*/> list = new List<BvTypeConstraint /*!*/>();
          if (this.constraints != null)
          {
            list.AddRange(this.constraints);
          }

          if (bt.constraints != null)
          {
            list.AddRange(bt.constraints);
          }

          BvTypeProxy np = new BvTypeProxy(this.tok, this.Name, Math.Max(this.MinBits, bt.MinBits), list);
          this.DefineProxy(np);
          bt.DefineProxy(np);
        }
        else if (this.MinBits <= bt.MinBits)
        {
          this.DefineProxy(bt);
        }
        else
        {
          bt.DefineProxy(this);
        }

        return true;
      }
      else if (that is ConstrainedProxy)
      {
        // only bitvector proxies can be unified with this BvTypeProxy
        return false;
      }
      else if (that is TypeProxy)
      {
        // define:  that.ProxyFor := this;
        return that.Unify(this, unifiableVariables, result);
      }

      return false;
    }

    private static int IncreaseBits(Type t, int to)
    {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBv && 0 <= to && MinBitsFor(t) <= to);
      Contract.Ensures(0 <= Contract.Result<int>() && Contract.Result<int>() <= to);

      if (t is TypeSynonymAnnotation)
      {
        return IncreaseBits(((TypeSynonymAnnotation) t).ExpandedType, to);
      }

      t = FollowProxy(t);
      if (t is BvType)
      {
        return to - t.BvBits;
      }
      else
      {
        BvTypeProxy p = (BvTypeProxy) t;
        Contract.Assert(p.MinBits <= to);
        if (p.MinBits < to)
        {
          BvTypeProxy q = new BvTypeProxy(p, to);
          p.DefineProxy(q);
        }

        return 0; // we were able to satisfy the request completely
      }
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      if (this.ProxyFor == null)
      {
        // check that the constraints are clean and do not contain any
        // of the substituted variables (otherwise, we are in big trouble)
        Contract.Assert(Contract.ForAll(constraints, c =>
          Contract.ForAll(subst.Keys, var =>
            !c.T0.FreeVariables.Contains(var) && !c.T1.FreeVariables.Contains(var))));
      }

      return base.Substitute(subst);
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsBv
    {
      get { return true; }
    }

    public override int BvBits
    {
      get
      {
        // This method is supposed to return the number of bits supplied, but unless the proxy has been resolved,
        // we only have a lower bound on the number of bits supplied.  But this method is not supposed to be
        // called until type checking has finished, at which time the minBits is stable.
        Type p = ProxyFor;
        if (p != null)
        {
          return p.BvBits;
        }
        else
        {
          return MinBits;
        }
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBvTypeProxy(this);
    }
  }

  // Proxy representing map types with a certain arity. Apart from the arity,
  // a number of constraints on the index and value type of the map type may
  // be known (such constraints result from applied select and store operations).
  // Because map type can be polymorphic (in the most general case, each index or
  // value type is described by a separate type parameter) any combination of
  // constraints can be satisfied.
  public class MapTypeProxy : ConstrainedProxy
  {
    public readonly int Arity;

    private readonly List<Constraint> /*!*/
      constraints = new List<Constraint>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(constraints != null);
    }


    // each constraint specifies that the given combination of argument/result
    // types must be a possible instance of the formal map argument/result types
    private struct Constraint
    {
      public readonly List<Type> /*!*/
        Arguments;

      public readonly Type /*!*/
        Result;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Arguments != null);
        Contract.Invariant(Result != null);
      }


      public Constraint(List<Type> arguments, Type result)
      {
        Contract.Requires(result != null);
        Contract.Requires(arguments != null);
        Arguments = arguments;
        Result = result;
      }

      public Constraint Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
      {
        Contract.Requires(Cce.NonNullDictionaryAndValues(varMap));
        List<Type> /*!*/
          args = new List<Type>();
        foreach (Type /*!*/ t in Arguments)
        {
          Contract.Assert(t != null);
          args.Add(t.Clone(varMap));
        }

        Type /*!*/
          res = Result.Clone(varMap);
        Contract.Assert(res != null);
        return new Constraint(args, res);
      }

      public bool Unify(MapType that,
        List<TypeVariable> /*!*/ unifiableVariables,
        IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ result)
      {
        Contract.Requires(unifiableVariables != null);
        Contract.Requires(Cce.NonNullDictionaryAndValues(result));
        Contract.Requires(that != null);
        Contract.Requires(Arguments.Count == that.Arguments.Count);
        Dictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
          subst = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
        foreach (TypeVariable /*!*/ tv in that.TypeParameters)
        {
          Contract.Assert(tv != null);
          TypeProxy proxy = new TypeProxy(Token.NoToken, tv.Name);
          subst.Add(tv, proxy);
        }

        bool good = true;
        for (int i = 0; i < that.Arguments.Count; i++)
        {
          Type t0 = that.Arguments[i].Substitute(subst);
          Type t1 = this.Arguments[i];
          good &= t0.Unify(t1, unifiableVariables, result);
        }

        good &= that.Result.Substitute(subst).Unify(this.Result, unifiableVariables, result);
        return good;
      }
    }

    public MapTypeProxy(IToken token, string name, int arity)
      : base(token, name, "mapproxy")
    {
      Contract.Requires(name != null);
      Contract.Requires(token != null);
      Contract.Requires(0 <= arity);
      this.Arity = arity;
    }

    private void AddConstraint(Constraint c)
    {
      Contract.Requires(c.Arguments.Count == Arity);

      Type f = ProxyFor;
      MapType mf = f as MapType;
      if (mf != null)
      {
        bool success = c.Unify(mf, new List<TypeVariable>(), new Dictionary<TypeVariable /*!*/, Type /*!*/>());
        Contract.Assert(success);
        return;
      }

      MapTypeProxy mpf = f as MapTypeProxy;
      if (mpf != null)
      {
        mpf.AddConstraint(c);
        return;
      }

      Contract.Assert(f == null); // no other types should occur as specialisations of this proxy

      constraints.Add(c);
    }

    public Type CheckArgumentTypes(List<Expr> /*!*/ actualArgs,
      out TypeParamInstantiation /*!*/ tpInstantiation,
      IToken /*!*/ typeCheckingSubject,
      string /*!*/ opName,
      TypecheckingContext /*!*/ tc)
    {
      Contract.Requires(actualArgs != null);
      Contract.Requires(typeCheckingSubject != null);
      Contract.Requires(opName != null);
      Contract.Requires(tc != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);


      Type f = ProxyFor;
      MapType mf = f as MapType;
      if (mf != null)
      {
        return mf.CheckArgumentTypes(actualArgs, out tpInstantiation, typeCheckingSubject, opName, tc);
      }

      MapTypeProxy mpf = f as MapTypeProxy;
      if (mpf != null)
      {
        return mpf.CheckArgumentTypes(actualArgs, out tpInstantiation, typeCheckingSubject, opName, tc);
      }

      Contract.Assert(f == null); // no other types should occur as specialisations of this proxy

      // otherwise, we just record the constraints given by this usage of the map type
      List<Type> /*!*/
        arguments = new List<Type>();
      foreach (Expr /*!*/ e in actualArgs)
      {
        Contract.Assert(e != null);
        arguments.Add(e.Type);
      }

      Type /*!*/
        result = new TypeProxy(tok, "result");
      Contract.Assert(result != null);
      AddConstraint(new Constraint(arguments, result));

      List<Type> /*!*/
        argumentsResult = new List<Type>();
      foreach (Expr /*!*/ e in actualArgs)
      {
        Contract.Assert(e != null);
        argumentsResult.Add(e.Type);
      }

      argumentsResult.Add(result);

      tpInstantiation = new MapTypeProxyParamInstantiation(this, argumentsResult);
      return result;
    }

    //-----------  Cloning  ----------------------------------

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Clone(varMap);
      }
      else
      {
        MapTypeProxy p2 = new MapTypeProxy(tok, Name, Arity);
        foreach (Constraint c in constraints)
        {
          p2.AddConstraint(c.Clone(varMap));
        }

        return p2; // the clone will have a name that ends with $mapproxy<n>$mapproxy<m> (hopefully)
      }
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      Type p = ProxyFor;
      if (p != null)
      {
        p.Emit(stream, contextBindingStrength);
      }
      else
      {
        stream.Write("[");
        string /*!*/
          sep = "";
        for (int i = 0; i < Arity; ++i)
        {
          stream.Write(sep);
          sep = ", ";
          stream.Write("?");
        }

        stream.Write("]?");
      }
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ result)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(cce.NonNullElements(result));
      Type p = ProxyFor;
      if (p != null)
      {
        return p.Unify(that, unifiableVariables, result);
      }

      // unify this with that, if possible
      that = that.Expanded;
      that = FollowProxy(that);

      if (this.ReallyOccursIn(that))
      {
        return false;
      }

      TypeVariable tv = that as TypeVariable;

      if (tv != null && unifiableVariables.Contains(tv))
      {
        return that.Unify(this, unifiableVariables, result);
      }

      if (object.ReferenceEquals(this, that))
      {
        return true;
      }
      else if (that is MapType)
      {
        MapType mapType = (MapType) that;
        if (mapType.Arguments.Count == Arity)
        {
          bool good = true;
          foreach (Constraint c in constraints)
          {
            good &= c.Unify(mapType, unifiableVariables, result);
          }

          if (good)
          {
            DefineProxy(mapType);
            return true;
          }
        }
      }
      else if (that is MapTypeProxy)
      {
        MapTypeProxy mt = (MapTypeProxy) that;
        if (mt.Arity == this.Arity)
        {
          // we propagate the constraints of this proxy to the more specific one
          foreach (Constraint c in constraints)
          {
            mt.AddConstraint(c);
          }

          DefineProxy(mt);
          return true;
        }
      }
      else if (that is ConstrainedProxy)
      {
        // only map-type proxies can be unified with this MapTypeProxy
        return false;
      }
      else if (that is TypeProxy)
      {
        // define:  that.ProxyFor := this;
        return that.Unify(this, unifiableVariables, result);
      }

      return false;
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      if (this.ProxyFor == null)
      {
        // check that the constraints are clean and do not contain any
        // of the substituted variables (otherwise, we are in big trouble)
        Contract.Assert(Contract.ForAll(constraints, c =>
          Contract.ForAll(subst.Keys, var =>
            Contract.ForAll(0, c.Arguments.Count, t => !c.Arguments[t].FreeVariables.Contains(var)) &&
            !c.Result.FreeVariables.Contains(var))));
      }

      return base.Substitute(subst);
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsMap
    {
      get { return true; }
    }

    public override MapType /*!*/ AsMap
    {
      get
      {
        Contract.Ensures(Contract.Result<MapType>() != null);

        Type p = ProxyFor;
        if (p != null)
        {
          return p.AsMap;
        }
        else
        {
          {
            Contract.Assert(false);
            throw new Cce.UnreachableException();
          } // what to do now?
        }
      }
    }

    public override int MapArity
    {
      get { return Arity; }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitMapTypeProxy(this);
    }
  }

  //=====================================================================

  // Used to annotate types with type synonyms that were used in the
  // original unresolved types. Such types should be considered as
  // equivalent to ExpandedType, the annotations are only used to enable
  // better pretty-printing
  public class TypeSynonymAnnotation : Type
  {
    public Type /*!*/
      ExpandedType;

    public readonly List<Type> /*!*/
      Arguments;

    // is set during resolution and determines whether the right number of arguments is given
    public readonly TypeSynonymDecl /*!*/
      Decl;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(ExpandedType != null);
      Contract.Invariant(Arguments != null);
      Contract.Invariant(Decl != null);
    }


    public TypeSynonymAnnotation(IToken /*!*/ token, TypeSynonymDecl /*!*/ decl, List<Type> /*!*/ arguments)
      : base(token)
    {
      Contract.Requires(token != null);
      Contract.Requires(decl != null);
      Contract.Requires(arguments != null);
      Contract.Requires(arguments.Count == decl.TypeParameters.Count);
      this.Decl = decl;
      this.Arguments = arguments;

      // build a substitution that can be applied to the definition of
      // the type synonym
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst =
          new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      for (int i = 0; i < arguments.Count; ++i)
      {
        subst.Add(decl.TypeParameters[i], arguments[i]);
      }

      ExpandedType = decl.Body.Substitute(subst);
    }

    private TypeSynonymAnnotation(IToken /*!*/ token, TypeSynonymDecl /*!*/ decl, List<Type> /*!*/ arguments,
      Type /*!*/ expandedType)
      : base(token)
    {
      Contract.Requires(token != null);
      Contract.Requires(decl != null);
      Contract.Requires(arguments != null);
      Contract.Requires(expandedType != null);

      this.Decl = decl;
      this.Arguments = arguments;
      this.ExpandedType = expandedType;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.Clone(varMap));
      }

      Type /*!*/
        newExpandedType = ExpandedType.Clone(varMap);
      Contract.Assert(newExpandedType != null);
      return new TypeSynonymAnnotation(tok, Decl, newArgs, newExpandedType);
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.CloneUnresolved());
      }

      return new TypeSynonymAnnotation(tok, Decl, newArgs);
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type /*!*/ that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(thisBoundVariables != null);
      //Contract.Requires(thatBoundVariables != null);
      return ExpandedType.Equals(that, thisBoundVariables, thatBoundVariables);
    }

    // used to skip leading type annotations
    internal override Type /*!*/ Expanded
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return ExpandedType.Expanded;
      }
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ result)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(unifiableVariables != null);
      //Contract.Requires(cce.NonNullElements(result));
      return ExpandedType.Unify(that, unifiableVariables, result);
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      if (subst.Count == 0)
      {
        return this;
      }

      List<Type> newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.Substitute(subst));
      }

      Type /*!*/
        newExpandedType = ExpandedType.Substitute(subst);
      Contract.Assert(newExpandedType != null);
      return new TypeSynonymAnnotation(tok, Decl, newArgs, newExpandedType);
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      return ExpandedType.GetHashCode(boundVariables);
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      CtorType.EmitCtorType(this.Decl.Name, Arguments, stream, contextBindingStrength);
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> resolvedArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        resolvedArgs.Add(t.ResolveType(rc));
      }

      return new TypeSynonymAnnotation(tok, Decl, resolvedArgs);
    }

    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

        return ExpandedType.FreeVariables;
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeProxy>>()));
        return ExpandedType.FreeProxies;
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsBasic
    {
      get { return ExpandedType.IsBasic; }
    }

    public override bool IsInt
    {
      get { return ExpandedType.IsInt; }
    }

    public override bool IsReal
    {
      get { return ExpandedType.IsReal; }
    }

    public override bool IsFloat
    {
      get { return ExpandedType.IsFloat; }
    }

    public override int FloatExponent
    {
      get { return ExpandedType.FloatExponent; }
    }

    public override int FloatSignificand
    {
      get { return ExpandedType.FloatSignificand; }
    }

    public override bool IsBool
    {
      get { return ExpandedType.IsBool; }
    }

    public override bool IsRMode
    {
      get { return ExpandedType.IsRMode; }
    }

    public override bool IsString
    {
      get { return ExpandedType.IsString; }
    }

    public override bool IsRegEx
    {
      get { return ExpandedType.IsRegEx; }
    }

    public override bool IsVariable
    {
      get { return ExpandedType.IsVariable; }
    }

    public override TypeVariable /*!*/ AsVariable
    {
      get
      {
        Contract.Ensures(Contract.Result<TypeVariable>() != null);
        return ExpandedType.AsVariable;
      }
    }

    public override bool IsCtor
    {
      get { return ExpandedType.IsCtor; }
    }

    public override CtorType /*!*/ AsCtor
    {
      get
      {
        Contract.Ensures(Contract.Result<CtorType>() != null);
        return ExpandedType.AsCtor;
      }
    }

    public override bool IsMap
    {
      get { return ExpandedType.IsMap; }
    }

    public override MapType /*!*/ AsMap
    {
      get
      {
        Contract.Ensures(Contract.Result<MapType>() != null);
        return ExpandedType.AsMap;
      }
    }

    public override bool IsUnresolved
    {
      get { return ExpandedType.IsUnresolved; }
    }

    public override UnresolvedTypeIdentifier /*!*/ AsUnresolved
    {
      get
      {
        Contract.Ensures(Contract.Result<UnresolvedTypeIdentifier>() != null);

        return ExpandedType.AsUnresolved;
      }
    }

    public override bool IsBv
    {
      get { return ExpandedType.IsBv; }
    }

    public override int BvBits
    {
      get { return ExpandedType.BvBits; }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTypeSynonymAnnotation(this);
    }
  }

  //=====================================================================

  public class CtorType : Type
  {
    public readonly List<Type> /*!*/
      Arguments;

    // is set during resolution and determines whether the right number of arguments is given
    public readonly TypeCtorDecl /*!*/
      Decl;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Arguments != null);
      Contract.Invariant(Decl != null);
    }


    public CtorType(IToken /*!*/ token, TypeCtorDecl /*!*/ decl, List<Type> /*!*/ arguments)
      : base(token)
    {
      Contract.Requires(token != null);
      Contract.Requires(decl != null);
      Contract.Requires(arguments != null);
      Contract.Requires(arguments.Count == decl.Arity);
      this.Decl = decl;
      this.Arguments = arguments;
    }

    public bool IsDatatype()
    {
      return Decl is DatatypeTypeCtorDecl;
    }

    public override bool IsSeq
    {
      get { return GetBuiltin() == "Seq"; }
    }

    // This attribute is used to tell Boogie that this type is built into SMT-LIB and should
    // be represented using the provided string (and also does not need to be explicitly declared).
    public string GetBuiltin()
    {
      return (this.Decl as ICarriesAttributes).FindStringAttribute("builtin");
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.Clone(varMap));
      }

      return new CtorType(tok, Decl, newArgs);
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.CloneUnresolved());
      }

      return new CtorType(tok, Decl, newArgs);
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      Type thatType = that as Type;
      if (thatType == null)
      {
        return false;
      }

      thatType = TypeProxy.FollowProxy(thatType.Expanded);
      // shortcut
      CtorType thatCtorType = thatType as CtorType;
      if (thatCtorType == null || !this.Decl.Equals(thatCtorType.Decl))
      {
        return false;
      }

      if (Arguments.Count == 0)
      {
        return true;
      }

      return base.Equals(thatType);
    }

    [Pure]
    public override bool Equals(Type /*!*/ that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      that = TypeProxy.FollowProxy(that.Expanded);
      CtorType thatCtorType = that as CtorType;
      if (thatCtorType == null || !this.Decl.Equals(thatCtorType.Decl))
      {
        return false;
      }

      for (int i = 0; i < Arguments.Count; ++i)
      {
        if (!Arguments[i].Equals(thatCtorType.Arguments[i],
          thisBoundVariables, thatBoundVariables))
        {
          return false;
        }
      }

      return true;
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ result)
    {
      that = that.Expanded;
      if (that is TypeProxy || that is TypeVariable)
      {
        return that.Unify(this, unifiableVariables, result);
      }

      CtorType thatCtorType = that as CtorType;
      if (thatCtorType == null || !thatCtorType.Decl.Equals(Decl))
      {
        return false;
      }
      else
      {
        bool good = true;
        for (int i = 0; i < Arguments.Count; ++i)
        {
          good &= Arguments[i].Unify(thatCtorType.Arguments[i], unifiableVariables, result);
        }

        return good;
      }
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      if (subst.Count == 0)
      {
        return this;
      }

      List<Type> newArgs = new List<Type>();
      lock (Arguments)
      {
        foreach (Type /*!*/ t in Arguments)
        {
          Contract.Assert(t != null);
          newArgs.Add(t.Substitute(subst));
        }
      }

      return new CtorType(tok, Decl, newArgs);
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      int res = 1637643879 * Decl.GetHashCode();
      foreach (Type /*!*/ t in Arguments.ToArray())
      {
        Contract.Assert(t != null);
        res = res * 3 + t.GetHashCode(boundVariables);
      }

      return res;
    }

    [Pure]
    public override int GetHashCode()
    {
      return base.GetHashCode();
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      EmitCtorType(this.Decl.Name, Arguments, stream, contextBindingStrength);
    }

    internal static void EmitCtorType(string name, List<Type> args, TokenTextWriter stream, int contextBindingStrength)
    {
      Contract.Requires(stream != null);
      Contract.Requires(args != null);
      Contract.Requires(name != null);
      int opBindingStrength = args.Count > 0 ? 0 : 2;
      if (opBindingStrength < contextBindingStrength)
      {
        stream.Write("(");
      }

      stream.Write("{0}", TokenTextWriter.SanitizeIdentifier(name));
      int i = args.Count;
      foreach (Type /*!*/ t in args)
      {
        Contract.Assert(t != null);
        stream.Write(" ");
        // use a lower binding strength for the last argument
        // to allow map-types without parentheses
        t.Emit(stream, i == 1 ? 1 : 2);
        i = i - 1;
      }

      if (opBindingStrength < contextBindingStrength)
      {
        stream.Write(")");
      }
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      List<Type> resolvedArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        resolvedArgs.Add(t.ResolveType(rc));
      }

      return new CtorType(tok, Decl, resolvedArgs);
    }

    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        List<TypeVariable> /*!*/
          res = new List<TypeVariable>();
        foreach (Type /*!*/ t in Arguments.ToArray())
        {
          Contract.Assert(t != null);
          res.AppendWithoutDups(t.FreeVariables);
        }

        return res;
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        List<TypeProxy /*!*/> /*!*/
          res = new List<TypeProxy /*!*/>();
        foreach (Type /*!*/ t in Arguments.ToArray())
        {
          Contract.Assert(t != null);
          AppendWithoutDups(res, t.FreeProxies);
        }

        return res;
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsCtor
    {
      get { return true; }
    }

    public override CtorType /*!*/ AsCtor
    {
      get { return this; }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitCtorType(this);
    }
  }

  //=====================================================================

  public class MapType : Type
  {
    // an invariant is that each of the type parameters has to occur as
    // free variable in at least one of the arguments
    public readonly List<TypeVariable> /*!*/
      TypeParameters;

    public readonly List<Type> /*!*/
      Arguments;

    public Type /*!*/
      Result;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(TypeParameters != null);
      Contract.Invariant(Arguments != null);
      Contract.Invariant(Result != null);
    }


    public MapType(IToken /*!*/ token, List<TypeVariable> /*!*/ typeParameters, List<Type> /*!*/ arguments,
      Type /*!*/ result)
      : base(token)
    {
      Contract.Requires(token != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(arguments != null);
      Contract.Requires(result != null);

      this.TypeParameters = typeParameters;
      this.Result = result;
      this.Arguments = arguments;
    }

    //-----------  Cloning  ----------------------------------
    // We implement our own clone-method, because bound type variables
    // have to be created in the right way. It is /not/ ok to just clone
    // everything recursively

    public override Type Clone(IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/ varMap)
    {
      //Contract.Requires(cce.NonNullElements(varMap));
      Contract.Ensures(Contract.Result<Type>() != null);
      IDictionary<TypeVariable /*!*/, TypeVariable /*!*/> /*!*/
        newVarMap =
          new Dictionary<TypeVariable /*!*/, TypeVariable /*!*/>();
      foreach (KeyValuePair<TypeVariable /*!*/, TypeVariable /*!*/> p in varMap)
      {
        Contract.Assert(Cce.NonNullElements(p));
        if (!TypeParameters.Contains(p.Key))
        {
          newVarMap.Add(p);
        }
      }

      List<TypeVariable> /*!*/
        newTypeParams = new List<TypeVariable>();
      foreach (TypeVariable /*!*/ var in TypeParameters)
      {
        Contract.Assert(var != null);
        TypeVariable /*!*/
          newVar = new TypeVariable(var.tok, var.Name);
        Contract.Assert(newVar != null);
        newVarMap.Add(var, newVar);
        newTypeParams.Add(newVar);
      }

      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.Clone(newVarMap));
      }

      Type /*!*/
        newResult = Result.Clone(newVarMap);
      Contract.Assert(newResult != null);

      return new MapType(this.tok, newTypeParams, newArgs, newResult);
    }

    public override Type CloneUnresolved()
    {
      Contract.Ensures(Contract.Result<Type>() != null);
      List<TypeVariable> /*!*/
        newTypeParams = new List<TypeVariable>();
      foreach (TypeVariable /*!*/ var in TypeParameters)
      {
        Contract.Assert(var != null);
        TypeVariable /*!*/
          newVar = new TypeVariable(var.tok, var.Name);
        Contract.Assert(newVar != null);
        newTypeParams.Add(newVar);
      }

      List<Type> /*!*/
        newArgs = new List<Type>();
      foreach (Type /*!*/ t in Arguments)
      {
        Contract.Assert(t != null);
        newArgs.Add(t.CloneUnresolved());
      }

      Type /*!*/
        newResult = Result.CloneUnresolved();
      Contract.Assert(newResult != null);

      return new MapType(this.tok, newTypeParams, newArgs, newResult);
    }

    //-----------  Equality  ----------------------------------

    [Pure]
    public override bool Equals(Type /*!*/ that,
      List<TypeVariable> /*!*/ thisBoundVariables,
      List<TypeVariable> /*!*/ thatBoundVariables)
    {
      that = TypeProxy.FollowProxy(that.Expanded);
      MapType thatMapType = that as MapType;
      if (thatMapType == null ||
          this.TypeParameters.Count != thatMapType.TypeParameters.Count ||
          this.Arguments.Count != thatMapType.Arguments.Count)
      {
        return false;
      }

      thisBoundVariables = thisBoundVariables.ToList();
      foreach (TypeVariable /*!*/ var in this.TypeParameters)
      {
        Contract.Assert(var != null);
        thisBoundVariables.Add(var);
      }

      thatBoundVariables = thatBoundVariables.ToList();
      foreach (TypeVariable /*!*/ var in thatMapType.TypeParameters)
      {
        Contract.Assert(var != null);
        thatBoundVariables.Add(var);
      }

      for (int i = 0; i < Arguments.Count; ++i)
      {
        if (!Arguments[i].Equals(thatMapType.Arguments[i],
          thisBoundVariables, thatBoundVariables))
        {
          return false;
        }
      }

      return this.Result.Equals(thatMapType.Result,
        thisBoundVariables, thatBoundVariables);
    }

    //-----------  Unification of types  -----------

    public override bool Unify(Type /*!*/ that,
      List<TypeVariable> /*!*/ unifiableVariables,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ result)
    {
      that = that.Expanded;
      if (that is TypeProxy || that is TypeVariable)
      {
        return that.Unify(this, unifiableVariables, result);
      }

      MapType thatMapType = that as MapType;
      if (thatMapType == null ||
          this.TypeParameters.Count != thatMapType.TypeParameters.Count ||
          this.Arguments.Count != thatMapType.Arguments.Count)
      {
        return false;
      }

      // treat the bound variables of the two map types as equal...
      Dictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst0 =
          new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      Dictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst1 =
          new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      List<TypeVariable> freshies = new List<TypeVariable>();
      for (int i = 0; i < this.TypeParameters.Count; i++)
      {
        TypeVariable tp0 = this.TypeParameters[i];
        TypeVariable tp1 = thatMapType.TypeParameters[i];
        TypeVariable freshVar = new TypeVariable(tp0.tok, tp0.Name);
        freshies.Add(freshVar);
        subst0.Add(tp0, freshVar);
        subst1.Add(tp1, freshVar);
      }

      // ... and then unify the domain and range types
      bool good = true;
      for (int i = 0; i < this.Arguments.Count; i++)
      {
        Type t0 = this.Arguments[i].Substitute(subst0);
        Type t1 = thatMapType.Arguments[i].Substitute(subst1);
        good &= t0.Unify(t1, unifiableVariables, result);
      }

      Type r0 = this.Result.Substitute(subst0);
      Type r1 = thatMapType.Result.Substitute(subst1);
      good &= r0.Unify(r1, unifiableVariables, result);

      // Finally, check that none of the bound variables has escaped
      if (good && freshies.Count != 0)
      {
        // This is done by looking for occurrences of the fresh variables in the
        // non-substituted types ...
        List<TypeVariable> freeVars = this.FreeVariables;
        foreach (TypeVariable fr in freshies)
        {
          if (freeVars.Contains(fr))
          {
            return false;
          } // fresh variable escaped
        }

        freeVars = thatMapType.FreeVariables;
        foreach (TypeVariable fr in freshies)
        {
          if (freeVars.Contains(fr))
          {
            return false;
          } // fresh variable escaped
        }

        // ... and in the resulting unifier of type variables
        foreach (KeyValuePair<TypeVariable /*!*/, Type /*!*/> pair in result)
        {
          Contract.Assert(Cce.NonNullElements(pair));
          freeVars = pair.Value.FreeVariables;
          foreach (TypeVariable fr in freshies)
          {
            if (freeVars.Contains(fr))
            {
              return false;
            } // fresh variable escaped          
          }
        }
      }

      return good;
    }

    //-----------  Substitution of free variables with types not containing bound variables  -----------------

    [Pure]
    private bool collisionsPossible(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(subst));
      // PR: could be written more efficiently
      return TypeParameters.Any(param =>
        subst.ContainsKey(param) || subst.Values.Any(val => val.FreeVariables.Contains(param)));
    }

    public override Type Substitute(IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ subst)
    {
      //Contract.Requires(cce.NonNullElements(subst));
      Contract.Ensures(Contract.Result<Type>() != null);
      if (subst.Count == 0)
      {
        return this;
      }

      // there are two cases in which we have to be careful:
      // * a variable to be substituted is shadowed by a variable binder
      // * a substituted term contains variables that are bound in the
      //   type (variable capture)
      //
      // in both cases, we first clone the type to ensure that bound
      // variables are fresh

      if (collisionsPossible(subst))
      {
        MapType /*!*/
          newType = (MapType) this.Clone();
        Contract.Assert(newType != null);
        Contract.Assert(newType.Equals(this) && !newType.collisionsPossible(subst));
        return newType.Substitute(subst);
      }

      List<Type> newArgs = new List<Type>();
      lock (Arguments)
      {
        foreach (Type /*!*/ t in Arguments)
        {
          Contract.Assert(t != null);
          newArgs.Add(t.Substitute(subst));
        }
      }

      Type /*!*/
        newResult = Result.Substitute(subst);
      Contract.Assert(newResult != null);

      return new MapType(tok, TypeParameters, newArgs, newResult);
    }

    //-----------  Hashcodes  ----------------------------------

    [Pure]
    public override int GetHashCode(List<TypeVariable> boundVariables)
    {
      //Contract.Requires(boundVariables != null);
      int res = 7643761 * TypeParameters.Count + 65121 * Arguments.Count;

      boundVariables = boundVariables.ToList();
      foreach (TypeVariable /*!*/ var in this.TypeParameters)
      {
        Contract.Assert(var != null);
        boundVariables.Add(var);
      }

      foreach (Type /*!*/ t in Arguments.ToArray())
      {
        Contract.Assert(t != null);
        res = res * 5 + t.GetHashCode(boundVariables);
      }

      res = res * 7 + Result.GetHashCode(boundVariables);

      return res;
    }

    //-----------  Linearisation  ----------------------------------

    public override void Emit(TokenTextWriter stream, int contextBindingStrength)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);

      const int opBindingStrength = 1;
      if (opBindingStrength < contextBindingStrength)
      {
        stream.Write("(");
      }

      EmitOptionalTypeParams(stream, TypeParameters);

      stream.Write("[");
      Arguments.Emit(stream, ","); // default binding strength of 0 is ok
      stream.Write("]");
      Result.Emit(stream); // default binding strength of 0 is ok

      if (opBindingStrength < contextBindingStrength)
      {
        stream.Write(")");
      }
    }

    //-----------  Resolution  ----------------------------------

    public override Type ResolveType(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      int previousState = rc.TypeBinderState;
      try
      {
        foreach (TypeVariable /*!*/ v in TypeParameters)
        {
          Contract.Assert(v != null);
          rc.AddTypeBinder(v);
        }

        List<Type> resolvedArgs = new List<Type>();
        foreach (Type /*!*/ ty in Arguments)
        {
          Contract.Assert(ty != null);
          resolvedArgs.Add(ty.ResolveType(rc));
        }

        Type resolvedResult = Result.ResolveType(rc);

        CheckBoundVariableOccurrences(TypeParameters,
          resolvedArgs, new List<Type> {resolvedResult},
          this.tok, "map arguments",
          rc);

        // sort the type parameters so that they are bound in the order of occurrence
        List<TypeVariable> /*!*/
          sortedTypeParams = SortTypeParams(TypeParameters, resolvedArgs, resolvedResult);
        Contract.Assert(sortedTypeParams != null);
        return new MapType(tok, sortedTypeParams, resolvedArgs, resolvedResult);
      }
      finally
      {
        rc.TypeBinderState = previousState;
      }
    }

    public override List<TypeVariable> /*!*/ FreeVariables
    {
      get
      {
        List<TypeVariable> /*!*/
          res = FreeVariablesIn(Arguments.ToList());
        Contract.Assert(res != null);
        res.AppendWithoutDups(Result.FreeVariables);
        foreach (TypeVariable /*!*/ v in TypeParameters.ToArray())
        {
          Contract.Assert(v != null);
          res.Remove(v);
        }

        return res;
      }
    }

    public override List<TypeProxy /*!*/> /*!*/ FreeProxies
    {
      get
      {
        List<TypeProxy /*!*/> /*!*/
          res = new List<TypeProxy /*!*/ /*!*/>();
        foreach (Type /*!*/ t in Arguments.ToArray())
        {
          Contract.Assert(t != null);
          AppendWithoutDups(res, t.FreeProxies);
        }

        AppendWithoutDups(res, Result.FreeProxies);
        return res;
      }
    }

    //-----------  Getters/Issers  ----------------------------------

    public override bool IsMap
    {
      get { return true; }
    }

    public override MapType /*!*/ AsMap
    {
      get { return this; }
    }

    public override int MapArity
    {
      get { return Arguments.Count; }
    }

    //------------  Match formal argument types of the map
    //------------  on concrete types, substitute the result into the
    //------------  result type. Null is returned if so many type checking
    //------------  errors occur that the situation is hopeless

    public Type CheckArgumentTypes(List<Expr> /*!*/ actualArgs,
      out TypeParamInstantiation /*!*/ tpInstantiation,
      IToken /*!*/ typeCheckingSubject,
      string /*!*/ opName,
      TypecheckingContext /*!*/ tc)
    {
      Contract.Requires(actualArgs != null);
      Contract.Requires(typeCheckingSubject != null);

      Contract.Requires(opName != null);
      Contract.Requires(tc != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      List<Type> actualResult =
        Type.CheckArgumentTypes(TypeParameters, out var actualTypeParams, Arguments, actualArgs,
          new List<Type> {Result}, null, typeCheckingSubject, opName, tc);
      if (actualResult == null)
      {
        tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
        return null;
      }
      else
      {
        Contract.Assert(actualResult.Count == 1);
        tpInstantiation = SimpleTypeParamInstantiation.From(TypeParameters, actualTypeParams);
        return actualResult[0];
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitMapType(this);
    }
  }

  //---------------------------------------------------------------------

  public enum SimpleType
  {
    Int,
    Real,
    Bool,
    RMode,
    String,
    RegEx
  }


  //=====================================================================

  // Interface for representing the instantiations of type parameters of
  // polymorphic functions or maps. We introduce an own interface for this
  // instead of using a simple list or dictionary, because in some cases
  // (due to the type proxies for map types) the actual number and instantiation
  // of type parameters can only be determined very late.
  [ContractClass(typeof(TypeParamInstantiationContracts))]
  public interface TypeParamInstantiation
  {
    // return what formal type parameters there are
    List<TypeVariable /*!*/> /*!*/ FormalTypeParams { get; }

    // given a formal type parameter, return the actual instantiation
    Type /*!*/ this[TypeVariable /*!*/ var] { get; }
  }

  [ContractClassFor(typeof(TypeParamInstantiation))]
  public abstract class TypeParamInstantiationContracts : TypeParamInstantiation
  {
    #region TypeParamInstantiation Members

    public List<TypeVariable> FormalTypeParams
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeVariable>>()));
        throw new NotImplementedException();
      }
    }

    public Type this[TypeVariable var]
    {
      get
      {
        Contract.Requires(var != null);
        Contract.Ensures(Contract.Result<Type>() != null);

        throw new NotImplementedException();
      }
    }

    #endregion
  }


  public class SimpleTypeParamInstantiation : TypeParamInstantiation
  {
    private readonly List<TypeVariable /*!*/> /*!*/
      TypeParams;

    [ContractInvariantMethod]
    void TypeParamsInvariantMethod()
    {
      Contract.Invariant(Cce.NonNullElements(TypeParams));
    }

    private readonly IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
      Instantiations;

    [ContractInvariantMethod]
    void InstantiationsInvariantMethod()
    {
      Contract.Invariant(Cce.NonNullDictionaryAndValues(Instantiations));
    }

    public SimpleTypeParamInstantiation(List<TypeVariable /*!*/> /*!*/ typeParams,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ instantiations)
    {
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Requires(Cce.NonNullDictionaryAndValues(instantiations));
      this.TypeParams = typeParams;
      this.Instantiations = instantiations;
    }

    public static TypeParamInstantiation /*!*/
      From(List<TypeVariable> typeParams, List<Type /*!*/> /*!*/ actualTypeParams)
    {
      Contract.Requires(Cce.NonNullElements(actualTypeParams));
      Contract.Requires(typeParams != null);
      Contract.Requires(typeParams.Count == actualTypeParams.Count);
      Contract.Ensures(Contract.Result<TypeParamInstantiation>() != null);

      if (typeParams.Count == 0)
      {
        return EMPTY;
      }

      List<TypeVariable /*!*/> /*!*/
        typeParamList = new List<TypeVariable /*!*/>();
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        dict = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      for (int i = 0; i < typeParams.Count; ++i)
      {
        typeParamList.Add(typeParams[i]);
        dict.Add(typeParams[i], actualTypeParams[i]);
      }

      return new SimpleTypeParamInstantiation(typeParamList, dict);
    }

    public static readonly TypeParamInstantiation EMPTY =
      new SimpleTypeParamInstantiation(new List<TypeVariable /*!*/>(),
        new Dictionary<TypeVariable /*!*/, Type /*!*/>());

    // return what formal type parameters there are
    public List<TypeVariable /*!*/> /*!*/ FormalTypeParams
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeVariable>>()));
        return TypeParams;
      }
    }

    // given a formal type parameter, return the actual instantiation
    public Type /*!*/ this[TypeVariable /*!*/ var]
    {
      get { return Instantiations[var]; }
    }
  }

  // Implementation of TypeParamInstantiation that refers to the current
  // value of a MapTypeProxy. This means that the values return by the
  // methods of this implementation can change in case the MapTypeProxy
  // receives further unifications.
  class MapTypeProxyParamInstantiation : TypeParamInstantiation
  {
    private readonly MapTypeProxy /*!*/
      Proxy;

    // the argument and result type of this particular usage of the map
    // type. these are necessary to derive the values of the type parameters
    private readonly List<Type> /*!*/
      ArgumentsResult;

    // field that is initialised once all necessary information is available
    // (the MapTypeProxy is instantiated to an actual type) and the instantiation
    // of a type parameter is queried
    private IDictionary<TypeVariable /*!*/, Type /*!*/> Instantiations = null;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Proxy != null);
      Contract.Invariant(ArgumentsResult != null);
      Contract.Invariant(Instantiations == null || Cce.NonNullDictionaryAndValues(Instantiations));
    }


    public MapTypeProxyParamInstantiation(MapTypeProxy /*!*/ proxy,
      List<Type> /*!*/ argumentsResult)
    {
      Contract.Requires(proxy != null);
      Contract.Requires(argumentsResult != null);
      this.Proxy = proxy;
      this.ArgumentsResult = argumentsResult;
    }

    // return what formal type parameters there are
    public List<TypeVariable /*!*/> /*!*/ FormalTypeParams
    {
      get
      {
        MapType realType = Proxy.ProxyFor as MapType;
        if (realType == null)
        {
          // no instantiation of the map type is known, which means
          // that the map type is assumed to be monomorphic
          return new List<TypeVariable /*!*/>();
        }
        else
        {
          return realType.TypeParameters.ToList();
        }
      }
    }

    // given a formal type parameter, return the actual instantiation
    public Type /*!*/ this[TypeVariable /*!*/ var]
    {
      get
      {
        // then there has to be an instantiation that is a polymorphic map type
        if (Instantiations == null)
        {
          MapType realType = Proxy.ProxyFor as MapType;
          Contract.Assert(realType != null);
          List<Type> /*!*/
            formalArgs = new List<Type>();
          foreach (Type /*!*/ t in realType.Arguments)
          {
            Contract.Assert(t != null);
            formalArgs.Add(t);
          }

          formalArgs.Add(realType.Result);
          Instantiations =
            Type.InferTypeParameters(realType.TypeParameters, formalArgs, ArgumentsResult);
        }

        return Instantiations[var];
      }
    }
  }
}