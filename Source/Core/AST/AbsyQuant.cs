using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.Threading;
using Set = Microsoft.Boogie.GSet<object>;

namespace Microsoft.Boogie
{
  //---------------------------------------------------------------------
  // Quantifiers and general binders
  //---------------------------------------------------------------------

  public enum BinderKind
  {
    Forall,
    Exists,
    Lambda
  }

  [ContractClassFor(typeof(BinderExpr))]
  abstract class BinderExprContracts : BinderExpr
  {
    public override BinderKind Kind
    {
      get { throw new NotImplementedException(); }
    }

    public BinderExprContracts() : base(null, null, null, null, null, false)
    {
    }

    public override Type ShallowType
    {
      get { throw new NotImplementedException(); }
    }
  }

  [ContractClass(typeof(BinderExprContracts))]
  public abstract class BinderExpr : Expr, ICarriesAttributes
  {
    public override int ContentHash => Util.GetHashCode(2099615205, Kind, TypeParameters.Count, Dummies.Count, Body.ContentHash);

    public List<TypeVariable> /*!*/
      TypeParameters;

    public List<Variable> /*!*/
      Dummies;

    public QKeyValue Attributes { get; set; }

    // FIXME: Protect the above Fields
    public Expr _Body;

    public Expr /*!*/ Body
    {
      get => _Body;
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Cannot change the Body of an immutable BinderExpr");
        }

        _Body = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(TypeParameters != null);
      Contract.Invariant(Dummies != null);
      Contract.Invariant(Body != null);
    }

    public BinderExpr(IToken /*!*/ tok, List<TypeVariable> /*!*/ typeParameters,
      List<Variable> /*!*/ dummies, QKeyValue kv, Expr /*!*/ body, bool immutable)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParameters.Count > 0);
      TypeParameters = typeParameters;
      Dummies = dummies;
      Attributes = kv;
      _Body = body;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    public abstract BinderKind Kind { get; }

    protected static ThreadLocal<bool> CompareAttributesAndTriggers = new(() => false);

    public static bool EqualWithAttributesAndTriggers(object a, object b)
    {
      CompareAttributesAndTriggers.Value = true;
      var res = object.Equals(a, b);
      Contract.Assert(CompareAttributesAndTriggers.Value);
      CompareAttributesAndTriggers.Value = false;
      return res;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      return BinderEquals(obj);
    }

    public bool BinderEquals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is BinderExpr) ||
          this.Kind != ((BinderExpr) obj).Kind)
      {
        return false;
      }

      var other = (BinderExpr) obj;

      return this.TypeParameters.SequenceEqual(other.TypeParameters)
             && this.Dummies.SequenceEqual(other.Dummies)
             && (!CompareAttributesAndTriggers.Value || object.Equals(this.Attributes, other.Attributes))
             && object.Equals(this.Body, other.Body);
    }

    [Pure]
    public override int GetHashCode()
    {
      if (Immutable)
      {
        return CachedHashCode;
      }
      else
      {
        return ComputeHashCode();
      }
    }

    [Pure]
    public override int ComputeHashCode()
    {
      // Note, we don't hash triggers and attributes

      // DO NOT USE Dummies.GetHashCode() because we want structurally
      // identical Expr to have the same hash code **not** identical references
      // to have the same hash code.
      int h = 0;
      foreach (var dummyVar in this.Dummies)
      {
        h = (53 * h) + dummyVar.GetHashCode();
      }

      h ^= this.Body.GetHashCode();

      // DO NOT USE TypeParameters.GetHashCode() because we want structural
      // identical Expr to have the same hash code **not** identical references
      // to have the same hash code.
      int h2 = 0;
      foreach (var typeParam in this.TypeParameters)
      {
        h2 = (97 * h2) + typeParam.GetHashCode();
      }

      h = h * 5 + h2;
      h *= ((int) Kind + 1);
      return h;
    }

    protected virtual void EmitTypeHint(TokenTextWriter stream)
    {
      Contract.Requires(stream != null);
    }

    protected virtual void EmitTriggers(TokenTextWriter stream)
    {
      Contract.Requires(stream != null);
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      stream.push();
      stream.Write(this, "({0}", Kind.ToString().ToLower());
      this.EmitTypeHint(stream);
      Type.EmitOptionalTypeParams(stream, TypeParameters);
      stream.Write(this, " ");
      this.Dummies.Emit(stream, true);
      stream.Write(" :: ");
      stream.sep();
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
      {
        kv.Emit(stream);
        stream.Write(" ");
      }

      this.EmitTriggers(stream);
      stream.sep();

      this.Body.Emit(stream);
      stream.Write(")");
      stream.pop();
    }

    protected virtual void ResolveTriggers(ResolutionContext rc)
    {
      Contract.Requires(rc != null);
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      if (rc.TriggerMode)
      {
        rc.Error(this, "quantifiers are not allowed in triggers");
      }

      int previousTypeBinderState = rc.TypeBinderState;
      try
      {
        foreach (TypeVariable /*!*/ v in TypeParameters)
        {
          Contract.Assert(v != null);
          rc.AddTypeBinder(v);
        }

        rc.PushVarContext();
        foreach (Variable /*!*/ v in Dummies)
        {
          Contract.Assert(v != null);
          v.Register(rc);
          v.Resolve(rc);
        }

        for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
        {
          kv.Resolve(rc);
        }

        this.ResolveTriggers(rc);
        Body.Resolve(rc);
        rc.PopVarContext();

        // establish a canonical order of the type parameters
        this.TypeParameters = Type.SortTypeParams(TypeParameters,
          Dummies.Select(Item => Item.TypedIdent.Type).ToList(), null);
      }
      finally
      {
        rc.TypeBinderState = previousTypeBinderState;
      }
    }

    public override void ComputeFreeVariables(Set freeVars)
    {
      //Contract.Requires(freeVars != null);
      ComputeBinderFreeVariables(TypeParameters, Dummies, Body, null, Attributes, freeVars);
    }

    public static void ComputeBinderFreeVariables(List<TypeVariable> typeParameters, List<Variable> dummies, Expr body,
      Trigger triggers, QKeyValue attributes, Set freeVars)
    {
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);

      foreach (var v in dummies)
      {
        Contract.Assert(v != null);
        Contract.Assert(!freeVars[v]);
      }

      body.ComputeFreeVariables(freeVars);
      for (var trig = triggers; trig != null; trig = trig.Next)
      {
        foreach (var e in trig.Tr)
        {
          e.ComputeFreeVariables(freeVars);
        }
      }

      for (var a = attributes; a != null; a = a.Next)
      {
        foreach (var o in a.Params)
        {
          var e = o as Expr;
          if (e != null)
          {
            e.ComputeFreeVariables(freeVars);
          }
        }
      }

      foreach (var v in dummies)
      {
        freeVars.AddRange(v.TypedIdent.Type.FreeVariables);
      }

      freeVars.RemoveRange(dummies);
      freeVars.RemoveRange(typeParameters);
    }

    protected List<TypeVariable> GetUnmentionedTypeParameters()
    {
      Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);
      List<TypeVariable> /*!*/
        dummyParameters = Type.FreeVariablesIn(Dummies.Select(Item => Item.TypedIdent.Type).ToList());
      Contract.Assert(dummyParameters != null);
      List<TypeVariable> /*!*/
        unmentionedParameters = new List<TypeVariable>();
      foreach (TypeVariable /*!*/ var in TypeParameters)
      {
        Contract.Assert(var != null);
        if (!dummyParameters.Contains(var))
        {
          unmentionedParameters.Add(var);
        }
      }

      return unmentionedParameters;
    }
  }

  public class QKeyValue : Absy
  {
    public readonly string /*!*/
      Key;

    private readonly List<object /*!*/> /*!*/
      _params; // each element is either a string or an Expr

    public void AddParam(object p)
    {
      Contract.Requires(p != null);
      this._params.Add(p);
    }

    public void AddParams(IEnumerable<object> ps)
    {
      Contract.Requires(Cce.NonNullElements(ps));
      this._params.AddRange(ps);
    }

    public void ClearParams()
    {
      this._params.Clear();
    }

    public IList<object> Params
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<IList<object>>()));
        Contract.Ensures(Contract.Result<IList<object>>().IsReadOnly);
        return this._params.AsReadOnly();
      }
    }

    public QKeyValue Next;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Key != null);
      Contract.Invariant(Cce.NonNullElements(this._params));
    }

    public QKeyValue(IToken tok, string key, IList<object /*!*/> /*!*/ parameters, QKeyValue next)
      : base(tok)
    {
      Contract.Requires(key != null);
      Contract.Requires(tok != null);
      Contract.Requires(Cce.NonNullElements(parameters));
      Key = key;
      this._params = new List<object>(parameters);
      Next = next;
    }

    public void Emit(TokenTextWriter stream)
    {
      Contract.Requires(stream != null);
      stream.Write("{:");
      stream.Write(Key);
      string sep = " ";
      foreach (object p in Params)
      {
        stream.Write(sep);
        sep = ", ";
        if (p is string)
        {
          stream.Write("\"");
          stream.Write((string) p);
          stream.Write("\"");
        }
        else
        {
          ((Expr) p).Emit(stream);
        }
      }

      stream.Write("}");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);

      if ((Key == "minimize" || Key == "maximize") && Params.Count != 1)
      {
        rc.Error(this, "attributes :minimize and :maximize accept only one argument");
      }

      if (Key == "verified_under" && Params.Count != 1)
      {
        rc.Error(this, "attribute :verified_under accepts only one argument");
      }

      if (Key == CivlAttributes.LAYER)
      {
        foreach (var o in Params)
        {
          if (o is LiteralExpr l && l.isBigNum)
          {
            var n = l.asBigNum;
            if (n.IsNegative)
            {
              rc.Error(this, "layer must be non-negative");
            }
            else if (!n.InInt32)
            {
              rc.Error(this, "layer is too large (max value is Int32.MaxValue)");
            }
          }
          else
          {
            rc.Error(this, "layer must be a non-negative integer");
          }
        }
      }

      foreach (object p in Params)
      {
        if (p is Expr)
        {
          var oldCtxtState = rc.StateMode;
          if (oldCtxtState == ResolutionContext.State.Single)
          {
            rc.StateMode = ResolutionContext.State.Two;
          }

          ((Expr) p).Resolve(rc);
          if (oldCtxtState != rc.StateMode)
          {
            rc.StateMode = oldCtxtState;
          }
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (object p in Params)
      {
        var expr = p as Expr;
        if (expr != null)
        {
          expr.Typecheck(tc);
        }

        if ((Key == "minimize" || Key == "maximize")
            && (expr == null || !(expr.Type.IsInt || expr.Type.IsReal || expr.Type.IsBv)))
        {
          tc.Error(this, "attributes :minimize and :maximize accept only one argument of type int, real or bv");
          break;
        }

        if (Key == "verified_under" && (expr == null || !expr.Type.IsBool))
        {
          tc.Error(this, "attribute :verified_under accepts only one argument of type bool");
          break;
        }
      }
    }

    public void AddLast(QKeyValue other)
    {
      Contract.Requires(other != null);
      QKeyValue current = this;
      while (current.Next != null)
      {
        current = current.Next;
      }

      current.Next = other;
    }

    public static QKeyValue FindAttribute(QKeyValue kv, Func<QKeyValue, bool> property)
    {
      for (; kv != null; kv = kv.Next)
      {
        if (property(kv))
        {
          return kv;
        }
      }
      return null;
    }

    // Look for {:name string} in list of attributes.
    [Pure]
    public static string FindStringAttribute(QKeyValue kv, string name)
    {
      Contract.Requires(name != null);
      kv = FindAttribute(kv, qkv => qkv.Key == name && qkv.Params.Count == 1 && qkv.Params[0] is string);
      if (kv != null)
      {
        Contract.Assert(kv.Params.Count == 1 && kv.Params[0] is string);
        return (string) kv.Params[0];
      }
      return null;
    }

    // Look for {:name expr} in list of attributes.
    public static Expr FindExprAttribute(QKeyValue kv, string name)
    {
      Contract.Requires(name != null);
      kv = FindAttribute(kv, qkv => qkv.Key == name && qkv.Params.Count == 1 && qkv.Params[0] is Expr);
      if (kv != null)
      {
        Contract.Assert(kv.Params.Count == 1 && kv.Params[0] is Expr);
        return (Expr) kv.Params[0];
      }
      return null;
    }

    // Return 'true' if {:name true} or {:name} is an attribute in 'kv'
    public static bool FindBoolAttribute(QKeyValue kv, string name)
    {
      Contract.Requires(name != null);
      kv = FindAttribute(kv, qkv => qkv.Key == name && (qkv.Params.Count == 0 ||
                                    (qkv.Params.Count == 1 && qkv.Params[0] is LiteralExpr &&
                                      ((LiteralExpr) qkv.Params[0]).IsTrue)));
      return kv != null;
    }

    public static int FindIntAttribute(QKeyValue kv, string name, int defl)
    {
      Contract.Requires(name != null);
      Expr e = FindExprAttribute(kv, name);
      LiteralExpr l = e as LiteralExpr;
      if (l != null && l.isBigNum)
      {
        return l.asBigNum.ToIntSafe;
      }

      return defl;
    }

    public override Absy Clone()
    {
      List<object> newParams = new List<object>();
      foreach (object o in Params)
      {
        newParams.Add(o);
      }

      return new QKeyValue(tok, Key, newParams, (Next == null) ? null : (QKeyValue) Next.Clone());
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitQKeyValue(this);
    }

    public override bool Equals(object obj)
    {
      var other = obj as QKeyValue;
      if (other == null)
      {
        return false;
      }
      else
      {
        return Key == other.Key && object.Equals(Params, other.Params) &&
               (Next == null
                 ? other.Next == null
                 : object.Equals(Next, other.Next));
      }
    }

    public override int GetHashCode()
    {
      throw new NotImplementedException();
    }
  }

  public class Trigger : Absy
  {
    public readonly bool Pos;
    [Rep] private List<Expr> /*!*/ tr;

    public IList<Expr> /*!*/ Tr
    {
      get
      {
        Contract.Ensures(Contract.Result<IList<Expr>>() != null);
        Contract.Ensures(Contract.Result<IList<Expr>>().Count >= 1);
        Contract.Ensures(this.Pos || Contract.Result<IList<Expr>>().Count == 1);
        return this.tr.AsReadOnly();
      }
      set
      {
        Contract.Requires(value != null);
        Contract.Requires(value.Count >= 1);
        Contract.Requires(this.Pos || value.Count == 1);
        this.tr = new List<Expr>(value);
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this.tr != null);
      Contract.Invariant(this.tr.Count >= 1);
      Contract.Invariant(Pos || this.tr.Count == 1);
    }

    public Trigger Next;

    public Trigger(IToken /*!*/ tok, bool pos, IEnumerable<Expr> /*!*/ tr, Trigger next = null)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(tr != null);
      Contract.Requires(tr.Count() >= 1);
      Contract.Requires(pos || tr.Count() == 1);
      this.Pos = pos;
      this.Tr = new List<Expr>(tr);
      this.Next = next;
    }

    public void Emit(TokenTextWriter stream)
    {
      Contract.Requires(stream != null);
      stream.SetToken(this);
      Contract.Assert(this.Tr.Count >= 1);
      string /*!*/
        sep = Pos ? "{ " : "{:nopats ";
      foreach (Expr /*!*/ e in this.Tr)
      {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }

      stream.Write(" }");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      rc.TriggerMode = true;
      foreach (Expr /*!*/ e in this.Tr)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);

        // just a variable by itself is not allowed
        if (e is IdentifierExpr)
        {
          rc.Error(e, "a matching pattern must be more than just a variable by itself: {0}", e);
        }

        // the free-variable check is performed in the surrounding quantifier expression (because that's
        // where the bound variables are known)
      }

      rc.TriggerMode = false;
    }

    /// <summary>
    /// Add to "freeVars" the free variables in the triggering expressions.
    /// </summary>
    public void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      Contract.Requires(freeVars != null);
      foreach (Expr /*!*/ e in this.Tr)
      {
        Contract.Assert(e != null);
        e.ComputeFreeVariables(freeVars);
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (Expr /*!*/ e in this.Tr)
      {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }
    }

    public void AddLast(Trigger other)
    {
      Trigger current = this;
      while (current.Next != null)
      {
        current = current.Next;
      }

      current.Next = other;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitTrigger(this);
    }

    public override bool Equals(object obj)
    {
      var other = obj as Trigger;
      if (other == null)
      {
        return false;
      }
      else
      {
        return this.Tr.SequenceEqual(other.Tr) &&
               (Next == null ? other.Next == null : object.Equals(Next, other.Next));
      }
    }

    public override int GetHashCode()
    {
      int hash = 17;
      hash = hash * 23 + tr.GetHashCode();
      hash = hash * 23 + Pos.GetHashCode();
      if (Next != null)
      {
        hash = hash * 23 + Next.GetHashCode();
      }

      return hash;
    }
  }

  public class ForallExpr : QuantifierExpr
  {
    public ForallExpr(IToken /*!*/ tok, List<TypeVariable> /*!*/ typeParams,
      List<Variable> /*!*/ dummies, QKeyValue kv, Trigger triggers, Expr /*!*/ body, bool immutable = false)
      : base(tok, typeParams, dummies, kv, triggers, body, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParams.Count > 0);
    }

    public ForallExpr(IToken tok, List<Variable> dummies, Trigger triggers, Expr body, bool immutable = false)
      : base(tok, new List<TypeVariable>(), dummies, null, triggers, body, immutable)
    {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }

    public ForallExpr(IToken tok, List<Variable> dummies, Expr body, bool immutable = false)
      : base(tok, new List<TypeVariable>(), dummies, null, null, body, immutable)
    {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }

    public ForallExpr(IToken tok, List<TypeVariable> typeParams, List<Variable> dummies, Expr body,
      bool immutable = false)
      : base(tok, typeParams, dummies, null, null, body, immutable)
    {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count + typeParams.Count > 0);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitForallExpr(this);
    }

    public override BinderKind Kind
    {
      get { return BinderKind.Forall; }
    }
  }

  public class ExistsExpr : QuantifierExpr
  {
    public ExistsExpr(IToken /*!*/ tok, List<TypeVariable> /*!*/ typeParams, List<Variable> /*!*/ dummies,
      QKeyValue kv, Trigger triggers, Expr /*!*/ body, bool immutable = false)
      : base(tok, typeParams, dummies, kv, triggers, body, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(typeParams != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParams.Count > 0);
    }

    public ExistsExpr(IToken tok, List<Variable> dummies, Trigger triggers, Expr body, bool immutable = false)
      : base(tok, new List<TypeVariable>(), dummies, null, triggers, body, immutable)
    {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }

    public ExistsExpr(IToken tok, List<Variable> dummies, Expr body, bool immutable = false)
      : base(tok, new List<TypeVariable>(), dummies, null, null, body, immutable)
    {
      Contract.Requires(body != null);
      Contract.Requires(dummies != null);
      Contract.Requires(tok != null);
      Contract.Requires(dummies.Count > 0);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitExistsExpr(this);
    }

    public override BinderKind Kind
    {
      get { return BinderKind.Exists; }
    }
  }

  public abstract class QuantifierExpr : BinderExpr
  {
    public Trigger Triggers;

    static int SkolemIds = -1;

    public static int GetNextSkolemId()
    {
      return System.Threading.Interlocked.Increment(ref SkolemIds);
    }

    public readonly int SkolemId;

    public QuantifierExpr(IToken /*!*/ tok, List<TypeVariable> /*!*/ typeParameters,
      List<Variable> /*!*/ dummies, QKeyValue kv, Trigger triggers, Expr /*!*/ body, bool immutable)
      : base(tok, typeParameters, dummies, kv, body, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParameters.Count > 0);

      Contract.Assert((this is ForallExpr) || (this is ExistsExpr));

      Triggers = triggers;
      SkolemId = GetNextSkolemId();
    }

    protected override void EmitTriggers(TokenTextWriter stream)
    {
      //Contract.Requires(stream != null);
      stream.push();
      for (Trigger tr = this.Triggers; tr != null; tr = tr.Next)
      {
        tr.Emit(stream);
        stream.Write(" ");
        stream.sep();
      }

      stream.pop();
    }

    // if the user says ( forall x :: forall y ::  ... ) and specifies *no* triggers, we transform it to
    // (forall x, y ::  ... ) which may help the prover to pick trigger terms
    //
    // (Note: there used to be a different criterion here, which allowed merging when triggers were specified, which could cause prover errors due to resulting unbound variables in the triggers)
    private void MergeAdjacentQuantifier()
    {
      QuantifierExpr qbody = Body as QuantifierExpr;
      if (!(qbody != null && (qbody is ForallExpr) == (this is ForallExpr) && Triggers == null))
      {
        return;
      }

      qbody.MergeAdjacentQuantifier();
      if (this.Triggers != null || qbody.Triggers != null)
      {
        return;
      }

      Body = qbody.Body;
      TypeParameters.AddRange(qbody.TypeParameters);
      Dummies.AddRange(qbody.Dummies);
      Triggers = qbody.Triggers;
      if (qbody.Attributes != null)
      {
        if (Attributes == null)
        {
          Attributes = qbody.Attributes;
        }
        else
        {
          QKeyValue p = Attributes;
          while (p.Next != null)
          {
            p = p.Next;
          }

          p.Next = qbody.Attributes;
        }
      }
    }

    #region never triggers

    private class NeverTriggerCollector : ReadOnlyVisitor
    {
      QuantifierExpr /*!*/
        parent;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(parent != null);
      }

      public NeverTriggerCollector(QuantifierExpr p)
      {
        Contract.Requires(p != null);
        parent = p;
      }

      public override Expr VisitNAryExpr(NAryExpr node)
      {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        FunctionCall fn = node.Fun as FunctionCall;
        if (fn != null && Cce.NonNull(fn.Func).NeverTrigger)
        {
          parent.Triggers = new Trigger(fn.Func.tok, false, new List<Expr> {node}, parent.Triggers);
        }

        return base.VisitNAryExpr(node);
      }

      public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
      {
        // don't go into quantifier expression or its triggers, since the terms in there may have more bound variables
        // (note, with only the VisitBinderExpr override below, we'd still be visiting triggers, which we don't want to do)
        return node;
      }

      public override BinderExpr VisitBinderExpr(BinderExpr node)
      {
        // don't go into binder expression, since the terms in there may have more bound variables
        return node;
      }
    }

    private bool neverTriggerApplied;

    private void ApplyNeverTriggers()
    {
      if (neverTriggerApplied)
      {
        return;
      }

      neverTriggerApplied = true;

      for (Trigger t = Triggers; t != null; t = t.Next)
      {
        if (t.Pos)
        {
          return;
        }
      }

      NeverTriggerCollector visitor = new NeverTriggerCollector(this);
      visitor.VisitExpr(Body);
    }

    #endregion

    protected override void ResolveTriggers(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      for (Trigger tr = this.Triggers; tr != null; tr = tr.Next)
      {
        int prevErrorCount = rc.ErrorCount;
        tr.Resolve(rc);
        if (prevErrorCount == rc.ErrorCount)
        {
          // for positive triggers, make sure all bound variables are mentioned
          if (tr.Pos)
          {
            Set /*Variable*/
              freeVars = new Set /*Variable*/();
            tr.ComputeFreeVariables(freeVars);
            foreach (Variable /*!*/ v in Dummies)
            {
              Contract.Assert(v != null);
              if (!freeVars[v])
              {
                rc.Error(tr, "trigger must mention all quantified variables, but does not mention: {0}", v);
              }
            }
          }
        }
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      int oldErrorCount = rc.ErrorCount;

      this.MergeAdjacentQuantifier();

      base.Resolve(rc);

      if (oldErrorCount == rc.ErrorCount)
      {
        this.ApplyNeverTriggers();
      }
    }

    public override void ComputeFreeVariables(Set freeVars)
    {
      //Contract.Requires(freeVars != null);
      ComputeBinderFreeVariables(TypeParameters, Dummies, Body, Triggers, Attributes, freeVars);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
      {
        kv.Typecheck(tc);
      }

      for (Trigger tr = this.Triggers; tr != null; tr = tr.Next)
      {
        tr.Typecheck(tc);
      }

      Body.Typecheck(tc);
      Contract.Assert(Body.Type != null); // follows from postcondition of Expr.Typecheck
      if (!Body.Type.Unify(Type.Bool))
      {
        tc.Error(this, "quantifier body must be of type bool");
      }

      this.Type = Type.Bool;

      // Check that type parameters occur in the types of the
      // dummies, or otherwise in the triggers. This can only be
      // done after typechecking
      List<TypeVariable> /*!*/
        unmentionedParameters = GetUnmentionedTypeParameters();
      Contract.Assert(unmentionedParameters != null);

      if (unmentionedParameters.Count > 0)
      {
        // all the type parameters that do not occur in dummy types
        // have to occur in triggers

        for (Trigger tr = this.Triggers; tr != null; tr = tr.Next)
        {
          // for positive triggers, make sure all bound variables are mentioned
          if (tr.Pos)
          {
            Set /*Variable*/
              freeVars = new Set /*Variable*/();
            tr.ComputeFreeVariables(freeVars);
            foreach (TypeVariable /*!*/ v in unmentionedParameters)
            {
              Contract.Assert(v != null);
              if (!freeVars[v])
              {
                tc.Error(tr,
                  "trigger does not mention {0}, which does not occur in variables types either",
                  v);
              }
            }
          }
        }
      }
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Type.Bool;
      }
    }

    public override bool Equals(object obj)
    {
      var other = obj as QuantifierExpr;
      if (other == null)
      {
        return false;
      }
      else
      {
        return this.BinderEquals(obj) &&
               (!CompareAttributesAndTriggers.Value || object.Equals(Triggers, other.Triggers));
      }
    }

    public override int GetHashCode()
    {
      return base.GetHashCode();
    }
  }


  public class LambdaExpr : BinderExpr
  {
    public LambdaExpr(IToken /*!*/ tok, List<TypeVariable> /*!*/ typeParameters,
      List<Variable> /*!*/ dummies, QKeyValue kv, Expr /*!*/ body, bool immutable = false)
      : base(tok, typeParameters, dummies, kv, body, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(typeParameters != null);
      Contract.Requires(dummies != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count + typeParameters.Count > 0);
    }

    public override BinderKind Kind
    {
      get { return BinderKind.Lambda; }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      base.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
      {
        kv.Typecheck(tc);
      }

      Body.Typecheck(tc);
      Contract.Assert(Body.Type != null); // follows from postcondition of Expr.Typecheck

      List<Type> /*!*/
        argTypes = new List<Type>();
      foreach (Variable /*!*/ v in Dummies)
      {
        Contract.Assert(v != null);
        argTypes.Add(v.TypedIdent.Type);
      }

      this.Type = new MapType(this.tok, this.TypeParameters, argTypes, Body.Type);

      // Check that type parameters occur in the types of the
      // dummies, or otherwise in the triggers. This can only be
      // done after typechecking
      List<TypeVariable> /*!*/
        unmentionedParameters = GetUnmentionedTypeParameters();
      Contract.Assert(unmentionedParameters != null);

      if (unmentionedParameters.Count > 0)
      {
        tc.Error(this, "the type variable {0} does not occur in types of the lambda parameters",
          unmentionedParameters[0]);
      }
    }

    private Type mapType;

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        if (mapType == null)
        {
          List<Type> /*!*/
            argTypes = new List<Type>();
          foreach (Variable /*!*/ v in Dummies)
          {
            Contract.Assert(v != null);
            argTypes.Add(v.TypedIdent.Type);
          }

          mapType = new MapType(this.tok, this.TypeParameters, argTypes, Body.ShallowType);
        }

        return mapType;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitLambdaExpr(this);
    }
  }

  public class LetExpr : Expr, ICarriesAttributes
  {
    public LetExpr(IToken /*!*/ tok, List<Variable> /*!*/ dummies, List<Expr> rhss, QKeyValue kv, Expr /*!*/ body)
      : base(tok, false)
    {
      Contract.Requires(tok != null);
      Contract.Requires(dummies != null);
      Contract.Requires(rhss != null);
      Contract.Requires(body != null);
      Contract.Requires(dummies.Count > 0);
      Contract.Requires(rhss.Count > 0);
      Dummies = dummies;
      Rhss = rhss;
      Attributes = kv;
      Body = body;
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);

      if (Dummies.Count != Rhss.Count)
      {
        rc.Error(this.tok, "number of left-hand sides does not match number of right-hand sides");
      }

      foreach (var e in Rhss)
      {
        e.Resolve(rc);
      }

      rc.PushVarContext();
      foreach (var v in Dummies)
      {
        Contract.Assert(v != null);
        v.Register(rc);
        v.Resolve(rc);
      }

      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
      {
        kv.Resolve(rc);
      }

      Body.Resolve(rc);
      rc.PopVarContext();
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (var e in Rhss)
      {
        e.Typecheck(tc);
      }

      Contract.Assert(Dummies.Count == Rhss.Count); // enforced by resolution
      for (var i = 0; i < Dummies.Count; i++)
      {
        var lhs = Dummies[i];
        var rhs = Rhss[i];
        lhs.TypedIdent.Type = rhs.Type;
      }

      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
      {
        kv.Typecheck(tc);
      }

      Body.Typecheck(tc);
      Contract.Assert(Body.Type != null); // follows from postcondition of Expr.Typecheck
      this.Type = Body.Type;
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        return Body.ShallowType;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitLetExpr(this);
    }

    public List<Variable> /*!*/
      Dummies;

    public IList<Expr> /*!*/
      Rhss;

    public QKeyValue Attributes { get; set; }
    public Expr Body;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Dummies != null);
      Contract.Invariant(Rhss != null);
      Contract.Invariant(Body != null);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (!(obj is LetExpr))
      {
        return false;
      }

      var other = (LetExpr) obj;

      return this.Dummies.SequenceEqual(other.Dummies)
             && this.Rhss.SequenceEqual(other.Rhss)
             && object.Equals(this.Attributes, other.Attributes)
             && object.Equals(this.Body, other.Body);
    }

    [Pure]
    public override int GetHashCode()
    {
      return ComputeHashCode();
    }

    public override int ContentHash => Util.GetHashCode(1842378754, Dummies.Count,
      Rhss.Select(x => x.ContentHash).Aggregate(Body.ContentHash, Util.GetHashCode));

    [Pure]
    public override int ComputeHashCode()
    {
      // Note, we don't hash triggers and attributes

      // DO NOT USE Dummies.GetHashCode() because we want structurally
      // identical Expr to have the same hash code **not** identical references
      // to have the same hash code.
      int h = 0;
      foreach (var dummyVar in this.Dummies)
      {
        h = (53 * h) + dummyVar.GetHashCode();
      }

      h ^= this.Body.GetHashCode();

      return h;
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      stream.push();
      stream.Write(this, "(var ");

      string sep = "";
      stream.push();
      foreach (var v in Dummies)
      {
        stream.Write("{0}", sep);
        v.EmitVitals(stream, 0, true, false);
        sep = ", ";
        stream.sep();
      }

      stream.pop();

      stream.Write(" := ");
      this.Rhss.Emit(stream);
      stream.Write("; ");
      stream.sep();
      for (QKeyValue kv = this.Attributes; kv != null; kv = kv.Next)
      {
        kv.Emit(stream);
        stream.Write(" ");
      }

      stream.sep();

      this.Body.Emit(stream);
      stream.Write(")");
      stream.pop();
    }

    public override void ComputeFreeVariables(Set freeVars)
    {
      //Contract.Requires(freeVars != null);

      foreach (var e in Rhss)
      {
        e.ComputeFreeVariables(freeVars);
      }

      foreach (var v in Dummies)
      {
        Contract.Assert(v != null);
        Contract.Assert(!freeVars[v]);
      }

      foreach (var v in Dummies)
      {
        freeVars.AddRange(v.TypedIdent.Type.FreeVariables);
      }

      for (var a = Attributes; a != null; a = a.Next)
      {
        foreach (var o in a.Params)
        {
          var e = o as Expr;
          if (e != null)
          {
            e.ComputeFreeVariables(freeVars);
          }
        }
      }

      Body.ComputeFreeVariables(freeVars);
      freeVars.RemoveRange(Dummies);
    }
  }
}