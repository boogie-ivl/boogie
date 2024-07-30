using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.BaseTypes;
using Set = Microsoft.Boogie.GSet<object>; // not that the set used is not a set of Variable only, as it also contains TypeVariables

namespace Microsoft.Boogie
{
  //---------------------------------------------------------------------
  // Expressions
  //
  // For expressions, we override the Equals and GetHashCode method to
  // implement structural equality.  Note this is not logical equivalence
  // and is not modulo alpha-renaming.
  //---------------------------------------------------------------------


  [ContractClass(typeof(ExprContracts))]
  public abstract class Expr : Absy
  {
    public abstract int ContentHash { get; }
    
    public Expr(IToken /*!*/ tok, bool immutable)
      : base(tok)
    {
      Contract.Requires(tok != null);
      this.Immutable = immutable;
    }

    public void Emit(TokenTextWriter stream)
    {
      Contract.Requires(stream != null);
      Emit(stream, 0, false);
    }

    public enum Position
    {
      Pos,
      Neg,
      Neither
    }

    public static Position NegatePosition(Position p)
    {
      return p == Position.Neither ? Position.Neither : (p == Position.Neg ? Position.Pos : Position.Neg);
    }

    public Position pos = Position.Pos;

    /// <summary>
    /// If true the client is making a promise that this Expr will be
    /// treated immutably (i.e. once constructed it is never changed).
    /// This is currently not enforced but it should be!
    ///
    /// This allows the Expr's hash code to be cached making calls to
    /// GetHashCode() very cheap.
    /// </summary>
    /// <value><c>true</c> if immutable; otherwise, <c>false</c>.</value>
    public bool Immutable { get; private set; }

    /// <summary>
    /// Computes the hash code of this Expr skipping any cache.
    ///
    /// Sub classes should place their implementation of computing their hashcode
    /// here (making sure to call GetHashCode() not ComputeHashCode() on Expr for performance reasons)
    /// and have GetHashCode() use a cached result from ComputeHashCode() if the
    /// Expr was constructed to be immutable.
    /// </summary>
    /// <returns>The hash code.</returns>
    public abstract int ComputeHashCode();

    protected int CachedHashCode = 0;

    public abstract void Emit(TokenTextWriter /*!*/ wr, int contextBindingStrength, bool fragileContext);

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      System.IO.StringWriter buffer = new System.IO.StringWriter();
      using TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer,
        /*setTokens=*/ false, /*pretty=*/ false, PrintOptions.Default);
      this.Emit(stream, 0, false);

      return buffer.ToString();
    }

    /// <summary>
    /// Add to "freeVars" the free variables in the expression.
    /// </summary>
    public abstract void ComputeFreeVariables(Set /*Variable*/ /*!*/ freeVars);

    /// <summary>
    /// Filled in by the Typecheck method.  A value of "null" means a succeeding
    /// call to Typecheck has not taken place (that is, either Typecheck hasn't
    /// been called or Typecheck encountered an error in the expression to be
    /// typechecked).
    /// </summary>
    private Type _Type = null;

    public Type Type
    {
      get { return _Type; }
      set
      {
        if (_Type == null)
        {
          // Expr has never been type checked so always allow this
          _Type = value;
        }
        else
        {
          if (Immutable && !_Type.Equals(value))
          {
            throw new InvalidOperationException("Cannot change the Type of an Immutable Expr");
          }

          // Once the Type has been set (i.e. no longer null) we never change the reference
          // if this Expr is immutable, even if the Type is equivalent (i.e. _Type.Equals(newType))
          if (!Immutable)
          {
            _Type = value;
          }
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      Contract.Ensures(Type != null);
      // This body is added only because C# insists on it.  It should really be left out, as if TypeCheck still were abstract.
      // The reason for mentioning the method here at all is to give TypeCheck a postcondition for all expressions.
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    /// <summary>
    /// Returns the type of the expression, supposing that all its subexpressions are well typed.
    /// </summary>
    public abstract Type /*!*/ ShallowType { get; }

    // Handy syntactic sugar follows:

    public static NAryExpr Unary(IToken x, UnaryOperator.Opcode op, Expr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return new NAryExpr(x, new UnaryOperator(x, op), new List<Expr> {e1});
    }

    public static NAryExpr Binary(IToken x, BinaryOperator.Opcode op, Expr e0, Expr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return new NAryExpr(x, new BinaryOperator(x, op), new List<Expr> {e0, e1});
    }

    public static NAryExpr Binary(BinaryOperator.Opcode op, Expr e0, Expr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(e0.tok ?? e1.tok ?? Token.NoToken, op, e0, e1);
    }

    public static NAryExpr Eq(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Eq, e1, e2);
    }

    public static NAryExpr Neq(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Neq, e1, e2);
    }

    public static NAryExpr Le(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Le, e1, e2);
    }

    public static NAryExpr Ge(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Ge, e1, e2);
    }

    public static NAryExpr Lt(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Lt, e1, e2);
    }

    public static NAryExpr Gt(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Gt, e1, e2);
    }

    public static Expr And(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (e1 == true_)
      {
        return e2;
      }
      else if (e2 == true_)
      {
        return e1;
      }
      else if (e1 == false_ || e2 == false_)
      {
        return false_;
      }
      else
      {
        var res = Binary(BinaryOperator.Opcode.And, e1, e2);
        res.Type = Microsoft.Boogie.Type.Bool;
        res.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        return res;
      }
    }

    public static Expr Or(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (e1 == false_)
      {
        return e2;
      }
      else if (e2 == false_)
      {
        return e1;
      }
      else if (e1 == true_ || e2 == true_)
      {
        return true_;
      }
      else
      {
        return Binary(BinaryOperator.Opcode.Or, e1, e2);
      }
    }

    public static Expr Not(Expr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      NAryExpr nary = e1 as NAryExpr;

      if (e1 == true_)
      {
        return false_;
      }
      else if (e1 == false_)
      {
        return true_;
      }
      else if (nary != null)
      {
        if (nary.Fun is UnaryOperator)
        {
          UnaryOperator op = (UnaryOperator) nary.Fun;
          if (op.Op == UnaryOperator.Opcode.Not)
          {
            return cce.NonNull(nary.Args[0]);
          }
        }
        else if (nary.Fun is BinaryOperator)
        {
          BinaryOperator op = (BinaryOperator) nary.Fun;
          Expr arg0 = cce.NonNull(nary.Args[0]);
          Expr arg1 = cce.NonNull(nary.Args[1]);
          if (op.Op == BinaryOperator.Opcode.Eq)
          {
            return Neq(arg0, arg1);
          }
          else if (op.Op == BinaryOperator.Opcode.Neq)
          {
            return Eq(arg0, arg1);
          }
          else if (op.Op == BinaryOperator.Opcode.Lt)
          {
            return Le(arg1, arg0);
          }
          else if (op.Op == BinaryOperator.Opcode.Le)
          {
            return Lt(arg1, arg0);
          }
          else if (op.Op == BinaryOperator.Opcode.Ge)
          {
            return Gt(arg1, arg0);
          }
          else if (op.Op == BinaryOperator.Opcode.Gt)
          {
            return Ge(arg1, arg0);
          }
        }
      }

      return Unary(Token.NoToken, UnaryOperator.Opcode.Not, e1);
    }

    public static Expr Neg(Expr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return Unary(Token.NoToken, UnaryOperator.Opcode.Neg, e1);
    }

    public static NAryExpr Imp(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Imp, e1, e2);
    }

    public static NAryExpr Iff(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Iff, e1, e2);
    }

    public static NAryExpr Add(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Add, e1, e2);
    }

    public static NAryExpr Sub(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Sub, e1, e2);
    }

    public static NAryExpr Mul(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Mul, e1, e2);
    }

    public static NAryExpr Div(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Div, e1, e2);
    }

    public static NAryExpr Mod(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Mod, e1, e2);
    }

    public static NAryExpr RealDiv(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.RealDiv, e1, e2);
    }

    public static NAryExpr FloatDiv(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.FloatDiv, e1, e2);
    }

    public static NAryExpr Pow(Expr e1, Expr e2)
    {
      Contract.Requires(e2 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Binary(BinaryOperator.Opcode.Pow, e1, e2);
    }

    public static IdentifierExpr Ident(string name, Type type)
    {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
      return new IdentifierExpr(Token.NoToken, name, type);
    }

    public static IdentifierExpr Ident(Variable decl)
    {
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
      IdentifierExpr result = new IdentifierExpr(Token.NoToken, decl);
      return result;
    }

    public static LiteralExpr Literal(bool value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    public static LiteralExpr Literal(int value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, BigNum.FromInt(value));
    }

    public static LiteralExpr Literal(BigNum value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    public static LiteralExpr Literal(BigDec value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    public static LiteralExpr Literal(BigFloat value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    public static LiteralExpr Literal(RoundingMode value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    public static LiteralExpr Literal(String value)
    {
      Contract.Ensures(Contract.Result<LiteralExpr>() != null);
      return new LiteralExpr(Token.NoToken, value);
    }

    private static LiteralExpr /*!*/
      true_ = Literal(true);

    public static LiteralExpr /*!*/ True
    {
      get
      {
        Contract.Ensures(Contract.Result<LiteralExpr>() != null);
        return true_;
      }
    }

    private static LiteralExpr /*!*/
      false_ = Literal(false);

    public static LiteralExpr /*!*/ False
    {
      get
      {
        Contract.Ensures(Contract.Result<LiteralExpr>() != null);
        return false_;
      }
    }


    public static NAryExpr Select(Expr map, params Expr[] args)
    {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return SelectTok(Token.NoToken, map, args);
    }

    public static NAryExpr Select(Expr map, List<Expr /*!*/> /*!*/ args)
    {
      Contract.Requires(map != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return Select(map, args.ToArray());
    }

    // use a different name for this variant of the method
    // (-> some bug prevents overloading in this case)
    public static NAryExpr SelectTok(IToken x, Expr map, params Expr[] args)
    {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      List<Expr> /*!*/
        allArgs = new List<Expr>();
      allArgs.Add(map);
      foreach (Expr /*!*/ a in args)
      {
        Contract.Assert(a != null);
        allArgs.Add(a);
      }

      return new NAryExpr(x, new MapSelect(Token.NoToken, args.Length), allArgs);
    }

    public static NAryExpr Store(Expr map, params Expr[] args)
    {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      return StoreTok(Token.NoToken, map, args);
    }

    public static NAryExpr Store(Expr map, List<Expr /*!*/> /*!*/ indexes, Expr rhs)
    {
      Contract.Requires(rhs != null);
      Contract.Requires(map != null);
      Contract.Requires(cce.NonNullElements(indexes));
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      Expr[] /*!*/
        allArgs = new Expr[indexes.Count + 1];
      for (int i = 0; i < indexes.Count; ++i)
      {
        allArgs[i] = indexes[i];
      }

      allArgs[indexes.Count] = rhs;
      return Store(map, allArgs);
    }

    // use a different name for this variant of the method
    // (-> some bug prevents overloading in this case)
    public static NAryExpr /*!*/ StoreTok(IToken x, Expr map, params Expr[] args)
    {
      Contract.Requires(args != null);
      Contract.Requires(map != null);
      Contract.Requires(x != null);
      Contract.Requires(args.Length > 0); // zero or more indices, plus the value
      Contract.Ensures(Contract.Result<NAryExpr>() != null);

      List<Expr> /*!*/
        allArgs = new List<Expr>();
      allArgs.Add(map);
      foreach (Expr /*!*/ a in args)
      {
        Contract.Assert(a != null);
        allArgs.Add(a);
      }

      return new NAryExpr(x, new MapStore(Token.NoToken, args.Length - 1), allArgs);
    }

    public static NAryExpr CoerceType(IToken x, Expr subexpr, Type type)
    {
      Contract.Requires(type != null);
      Contract.Requires(subexpr != null);
      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<NAryExpr>() != null);
      List<Expr> /*!*/
        args = new List<Expr>();
      args.Add(subexpr);
      return new NAryExpr(x, new TypeCoercion(x, type), args);
    }

    public static Expr BinaryTreeAnd(List<Expr> terms)
    {
      return BinaryTreeAnd(terms, 0, terms.Count - 1);
    }

    private static Expr BinaryTreeAnd(List<Expr> terms, int start, int end)
    {
      if (start > end)
      {
        return Expr.True;
      }

      if (start == end)
      {
        return terms[start];
      }

      if (start + 1 == end)
      {
        return Expr.And(terms[start], terms[start + 1]);
      }

      var mid = (start + end) / 2;
      return Expr.And(BinaryTreeAnd(terms, start, mid), BinaryTreeAnd(terms, mid + 1, end));
    }

    public static Expr And(IEnumerable<Expr> conjuncts, bool returnNullIfEmpty = false)
    {
      Expr result = null;
      foreach (var c in conjuncts)
      {
        if (result != null)
        {
          result = LiteralExpr.And(result, c);
          result.Type = Type.Bool;
        }
        else
        {
          result = c;
          result.Type = Type.Bool;
        }
      }

      if (result == null && !returnNullIfEmpty)
      {
        result = Expr.True;
      }

      return result;
    }

    public static Expr Or(IEnumerable<Expr> disjuncts, bool returnNullIfEmpty = false)
    {
      Expr result = null;
      foreach (var d in disjuncts)
      {
        if (result != null)
        {
          result = LiteralExpr.Or(result, d);
          result.Type = Type.Bool;
        }
        else
        {
          result = d;
          result.Type = Type.Bool;
        }
      }

      if (result == null && !returnNullIfEmpty)
      {
        result = Expr.False;
      }

      return result;
    }
  }

  [ContractClassFor(typeof(Expr))]
  public abstract class ExprContracts : Expr
  {
    public ExprContracts() : base(null, /*immutable=*/ false)
    {
    }

    public override void Emit(TokenTextWriter wr, int contextBindingStrength, bool fragileContext)
    {
      Contract.Requires(wr != null);
      throw new NotImplementedException();
    }

    public override void ComputeFreeVariables(Set freeVars)
    {
      Contract.Requires(freeVars != null);
      throw new NotImplementedException();
    }

    public override Type ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        throw new NotImplementedException();
      }
    }
  }

  public class LiteralExpr : Expr
  {
    public override int ContentHash
    {
      get
      {
        if (Val is string stringValue) {
          return stringValue.GetDeterministicHashCode();
        }
        return Val.GetHashCode();
      }
    }

    public readonly object /*!*/
      Val; // false, true, a BigNum, a BigDec, a BigFloat, a BvConst, or a RoundingMode

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Val != null);
    }

    /// <summary>
    /// Creates a literal expression for the boolean value "b".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="b"></param>
    public LiteralExpr(IToken /*!*/ tok, bool b, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Val = b;
      Type = Type.Bool;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a literal expression for the integer value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken /*!*/ tok, BigNum v, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.Int;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a literal expression for the real value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken /*!*/ tok, BigDec v, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.Real;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a literal expression for the floating point value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken /*!*/ tok, BigFloat v, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.GetFloatType(v.SignificandSize, v.ExponentSize);
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a literal expression for the bitvector value "v".
    /// </summary>
    public LiteralExpr(IToken /*!*/ tok, BigNum v, int b, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= b);
      Val = new BvConst(v, b);
      Type = Type.GetBvType(b);
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a literal expression for the rounding mode value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken /*!*/ tok, RoundingMode v, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.RMode;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a literal expression for the string value "v".
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="v"></param>
    public LiteralExpr(IToken /*!*/ tok, String v, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Val = v;
      Type = Type.String;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is LiteralExpr))
      {
        return false;
      }

      LiteralExpr other = (LiteralExpr) obj;
      return object.Equals(this.Val, other.Val);
    }

    [Pure]
    public override int GetHashCode()
    {
      if (Immutable)
      {
        return this.CachedHashCode;
      }
      else
      {
        return ComputeHashCode();
      }
    }

    [Pure]
    public override int ComputeHashCode()
    {
      return this.Val.GetHashCode();
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      if (this.Val is bool)
      {
        stream.Write((bool) this.Val ? "true" : "false"); // correct capitalization
      }
      else if (Type.IsString)
      {
        stream.Write("\"" + cce.NonNull(this.Val.ToString()) + "\"");
      }
      else
      {
        stream.Write(cce.NonNull(this.Val.ToString()));
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      // nothing to resolve
    }

    public override void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      //Contract.Requires(freeVars != null);
      // no free variables to add
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      this.Type = ShallowType;
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        if (Val is bool)
        {
          return Type.Bool;
        }
        else if (Val is BigNum)
        {
          return Type.Int;
        }
        else if (Val is BigDec)
        {
          return Type.Real;
        }
        else if (Val is BigFloat)
        {
          BigFloat temp = (BigFloat) Val;
          return Type.GetFloatType(temp.SignificandSize, temp.ExponentSize);
        }
        else if (Val is BvConst)
        {
          return Type.GetBvType(((BvConst) Val).Bits);
        }
        else if (Val is RoundingMode)
        {
          return Type.RMode;
        }
        else if (Val is String)
        {
          return Type.String;
        }
        else
        {
          {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          } // like, where did this value come from?!
        }
      }
    }

    public bool IsFalse
    {
      get { return Val is bool && ((bool) Val) == false; }
    }

    public bool IsTrue
    {
      get { return Val is bool && ((bool) Val) == true; }
    }

    // should be eliminated after converting everything to BigNums
    private int asInt
    {
      get { return asBigNum.ToIntSafe; }
    }

    public bool isBigNum
    {
      get { return Val is BigNum; }
    }

    public BigNum asBigNum
    {
      get
      {
        Contract.Assert(isBigNum);
        return (BigNum) cce.NonNull(Val);
      }
    }

    public bool isBigDec
    {
      get { return Val is BigDec; }
    }

    public bool isBigFloat
    {
      get { return Val is BigFloat; }
    }

    public BigDec asBigDec
    {
      get
      {
        Contract.Assert(isBigDec);
        return (BigDec) cce.NonNull(Val);
      }
    }

    public BigFloat asBigFloat
    {
      get
      {
        Contract.Assert(isBigFloat);
        return (BigFloat) cce.NonNull(Val);
      }
    }

    public bool isBool
    {
      get { return Val is bool; }
    }

    public bool asBool
    {
      get
      {
        Contract.Assert(isBool);
        return (bool) cce.NonNull(Val);
      }
    }

    public bool isBvConst
    {
      get { return Val is BvConst; }
    }

    public BvConst asBvConst
    {
      get
      {
        Contract.Assert(isBvConst);
        return (BvConst) cce.NonNull(Val);
      }
    }

    public bool isRoundingMode
    {
      get { return Val is RoundingMode; }
    }

    public RoundingMode asRoundingMode
    {
      get
      {
        Contract.Assert(isRoundingMode);
        return (RoundingMode) cce.NonNull(Val);
      }
    }

    public bool isString
    {
      get { return Val is String; }
    }

    public String asString
    {
      get
      {
        Contract.Assert(isString);
        return (String) cce.NonNull(Val);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitLiteralExpr(this);
    }
  }

  public class BvConst
  {
    public readonly BigNum Value;
    public readonly int Bits;

    public BvConst(BigNum v, int b)
    {
      Contract.Assert(v.Signum >= 0);
      Value = v;
      Bits = b;
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return Value + "bv" + Bits;
    }

    [Pure]
    public string ToReadableString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      if (Value > BigNum.FromInt(10000))
      {
        string val = cce.NonNull(Value.ToString("x"));
        int pos = val.Length % 4;
        string res = "0x" + val.Substring(0, pos);
        Contract.Assert(res != null);
        while (pos < val.Length)
        {
          res += "." + val.Substring(pos, 4);
          pos += 4;
        }

        return res + ".bv" + Bits;
      }
      else
      {
        return ToString();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      BvConst other = obj as BvConst;
      if (other == null)
      {
        return false;
      }

      return Bits == other.Bits && Value == other.Value;
    }

    [Pure]
    public override int GetHashCode()
    {
      unchecked
      {
        return Value.GetHashCode() ^ Bits;
      }
    }
  }

  public class IdentifierExpr : Expr
  {
    private string _Name;

    public string Name
    {
      // identifier symbol
      get { return _Name; }
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Cannot change Name on Immutable Expr");
        }

        _Name = value;
      }
    }

    private Variable _Decl;

    public Variable Decl
    {
      // identifier declaration
      get { return _Decl; }
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Cannot change Decl on Immutable Expr");
        }

        _Decl = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Name != null);
    }


    /// <summary>
    /// Creates an unresolved identifier expression.
    /// </summary>
    public IdentifierExpr(IToken /*!*/ tok, string /*!*/ name, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      _Name = name;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates an unresolved identifier expression.
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="name"></param>
    /// <param name="type"></param>
    public IdentifierExpr(IToken /*!*/ tok, string /*!*/ name, Type /*!*/ type, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      _Name = name;
      Type = type;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    /// <summary>
    /// Creates a resolved identifier expression.
    /// </summary>
    /// <param name="tok"></param>
    /// <param name="d"></param>
    public IdentifierExpr(IToken /*!*/ tok, Variable /*!*/ d, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(d != null);
      _Name = cce.NonNull(d.Name);
      _Decl = d;
      Type = d.TypedIdent.Type;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is IdentifierExpr))
      {
        return false;
      }

      IdentifierExpr other = (IdentifierExpr) obj;
      return object.Equals(this.Name, other.Name) && object.Equals(this.Decl, other.Decl);
    }

    [Pure]
    public override int GetHashCode()
    {
      if (Immutable)
      {
        return this.CachedHashCode;
      }
      else
      {
        return ComputeHashCode();
      }
    }

    public override int ContentHash => 1;

    [Pure]
    public override int ComputeHashCode()
    {
      int h = this.Name == null ? 0 : this.Name.GetHashCode();
      h ^= this.Decl == null ? 0 : this.Decl.GetHashCode();
      return h;
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      if (stream.Options.PrintWithUniqueASTIds && !stream.UseForComputingChecksums)
      {
        stream.Write("{0}^^", this.Decl == null ? "NoDecl" : "h" + this.Decl.GetHashCode());
      }

      stream.Write(this, "{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
    }

    public override void Resolve(ResolutionContext rc)
    {
      if (Decl != null)
      {
        // already resolved, but re-resolve type just in case it came from an unresolved type
        if (Type != null)
        {
          Type = Type.ResolveType(rc);
        }

        return;
      }

      Decl = rc.LookUpVariable(Name);
      if (Decl == null)
      {
        rc.Error(this, "undeclared identifier: {0}", Name);
      }
      else if (rc.StateMode == ResolutionContext.State.StateLess && Decl is GlobalVariable)
      {
        rc.Error(this, "cannot refer to a global variable in this context: {0}", Name);
      }

      if (Type != null)
      {
        Type = Type.ResolveType(rc);
      }
    }

    public override void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      Contract.Assume(this.Decl != null);
      freeVars.Add(Decl);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      if (this.Decl != null)
      {
        // sanity check
        if (Type != null && !Type.Equals(Decl.TypedIdent.Type))
        {
          tc.Error(this, "internal error, shallow-type assignment was done incorrectly, {0}:{1} != {2}",
            Name, Type, Decl.TypedIdent.Type);
          {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          }
        }

        Type = Decl.TypedIdent.Type;
        if (Decl is Constant || Decl is BoundVariable)
        {
          return;
        }

        // Decl is GlobalVariable or LocalVariable or Formal
        if (tc.Proc is ActionDecl actionDecl)
        {
          if (Decl is GlobalVariable)
          {
            if (!tc.GlobalAccessOk)
            {
              tc.Error(this, $"global variable must be accessed inside old expression: {Decl.Name}");
            }
            var globalVarLayerRange = Decl.LayerRange;
            if (actionDecl.LayerRange.LowerLayer <= globalVarLayerRange.LowerLayer)
            {
              // a global variable introduced at layer n is visible to an action only at layers greater than n
              tc.Error(this,
                $"global variable must be introduced below the lower layer {actionDecl.LayerRange.LowerLayer} of action {actionDecl.Name}: {Decl.Name}");
            }
            else
            {
              if (tc.ExpectedLayerRange == null)
              {
                if (!actionDecl.LayerRange.Subset(globalVarLayerRange))
                {
                  tc.Error(this,
                    $"global variable must be available across all layers ({actionDecl.LayerRange}) of action {actionDecl.Name}: {Decl.Name}");
                }
              }
              else
              {
                if (!tc.ExpectedLayerRange.Subset(globalVarLayerRange))
                {
                  tc.Error(this, $"global variable must be available across all layers in {tc.ExpectedLayerRange}: {Decl.Name}");
                }
              }
            }
          }
        }
        else if (tc.Proc is YieldInvariantDecl yieldInvariantDecl)
        {
          if (Decl is GlobalVariable)
          {
            if (!Decl.LayerRange.Contains(yieldInvariantDecl.Layer))
            {
              tc.Error(this, $"variable not available at layer {yieldInvariantDecl.Layer}: {Decl.Name}");
            }
          }
        }
        else if (tc.Proc is YieldProcedureDecl)
        {
          if (Decl is GlobalVariable && !tc.GlobalAccessOk)
          {
            tc.Error(this, $"global variable must be accessed inside old expression: {Decl.Name}");
          }
          if (tc.ExpectedLayerRange != null && !tc.ExpectedLayerRange.Subset(Decl.LayerRange))
          {
            tc.Error(this, $"variable not available across layers in {tc.ExpectedLayerRange}: {Decl.Name}");
          }
        }
      }
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        Contract.Assert(Type != null);
        return Type;
      }
    }

    public sealed class ConstantFunApp
    {
      private IdentifierExpr /*!*/
        identifierExpr;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(identifierExpr != null);
        Contract.Invariant(emptyArgs != null);
      }

      public IdentifierExpr /*!*/ IdentifierExpr
      {
        get
        {
          Contract.Requires(IdentifierExpr != null);
          return identifierExpr;
        }
      }

      private static IList /*!*/
        emptyArgs = ArrayList.ReadOnly(cce.NonNull((IList /*!*/) new ArrayList()));

      public IList /*!*/ Arguments
      {
        get
        {
          Contract.Ensures(Contract.Result<IList>() != null);
          return emptyArgs;
        }
      }

      public ConstantFunApp(IdentifierExpr ie, Constant c)
      {
        Contract.Requires(c != null);
        Contract.Requires(ie != null);
        this.identifierExpr = ie;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitIdentifierExpr(this);
    }
  }

  public class OldExpr : Expr
  {
    private Expr _Expr;

    public override int ContentHash => Util.GetHashCode(262567431, Expr.ContentHash);

    public Expr /*!*/ Expr
    {
      get
      {
        return _Expr;
      }
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Cannot change Expr of an Immutable OldExpr");
        }

        _Expr = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Expr != null);
    }

    public OldExpr(IToken /*!*/ tok, Expr /*!*/ expr, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      _Expr = expr;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is OldExpr))
      {
        return false;
      }

      OldExpr other = (OldExpr) obj;
      return object.Equals(this.Expr, other.Expr);
    }

    [Pure]
    public override int GetHashCode()
    {
      if (Immutable)
      {
        return this.CachedHashCode;
      }
      else
      {
        return ComputeHashCode();
      }
    }

    public override int ComputeHashCode()
    {
      // FIXME: This is wrong, it's as if the OldExpr node isn't there at all
      return this.Expr == null ? 0 : this.Expr.GetHashCode();
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, "old(");
      this.Expr.Emit(stream);
      stream.Write(")");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      if (rc.StateMode != ResolutionContext.State.Two)
      {
        rc.Error(this, "old expressions allowed only in two-state contexts");
      }

      Expr.Resolve(rc);
    }

    public override void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      //Contract.Requires(freeVars != null);
      Expr.ComputeFreeVariables(freeVars);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      tc.InsideOld++;
      Expr.Typecheck(tc);
      tc.InsideOld--;
      Type = Expr.Type;
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Expr.ShallowType;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitOldExpr(this);
    }
  }

  [ContractClass(typeof(IAppliableVisitorContracts<>))]
  public interface IAppliableVisitor<T>
  {
    T Visit(UnaryOperator unaryOperator);
    T Visit(BinaryOperator binaryOperator);
    T Visit(FunctionCall functionCall);
    T Visit(MapSelect mapSelect);
    T Visit(MapStore mapStore);
    T Visit(TypeCoercion typeCoercion);
    T Visit(ArithmeticCoercion arithCoercion);
    T Visit(IfThenElse ifThenElse);
    T Visit(FieldAccess fieldAccess);
    T Visit(FieldUpdate fieldUpdate);
    T Visit(IsConstructor isConstructor);
  }

  [ContractClassFor(typeof(IAppliableVisitor<>))]
  public abstract class IAppliableVisitorContracts<T> : IAppliableVisitor<T>
  {
    #region IAppliableVisitor<T> Members

    public T Visit(UnaryOperator unaryOperator)
    {
      Contract.Requires(unaryOperator != null);
      throw new NotImplementedException();
    }

    public T Visit(BinaryOperator binaryOperator)
    {
      Contract.Requires(binaryOperator != null);
      throw new NotImplementedException();
    }

    public T Visit(FunctionCall functionCall)
    {
      Contract.Requires(functionCall != null);
      throw new NotImplementedException();
    }

    public T Visit(MapSelect mapSelect)
    {
      Contract.Requires(mapSelect != null);
      throw new NotImplementedException();
    }

    public T Visit(MapStore mapStore)
    {
      Contract.Requires(mapStore != null);
      throw new NotImplementedException();
    }

    public T Visit(TypeCoercion typeCoercion)
    {
      Contract.Requires(typeCoercion != null);
      throw new NotImplementedException();
    }

    public T Visit(ArithmeticCoercion arithCoercion)
    {
      Contract.Requires(arithCoercion != null);
      throw new NotImplementedException();
    }

    public T Visit(IfThenElse ifThenElse)
    {
      Contract.Requires(ifThenElse != null);
      throw new NotImplementedException();
    }

    public T Visit(FieldAccess fieldAccess)
    {
      Contract.Requires(fieldAccess != null);
      throw new NotImplementedException();
    }

    public T Visit(FieldUpdate fieldUpdate)
    {
      Contract.Requires(fieldUpdate != null);
      throw new NotImplementedException();
    }
    
    public T Visit(IsConstructor isConstructor)
    {
      Contract.Requires(isConstructor != null);
      throw new NotImplementedException();
    }
    #endregion
  }

  [ContractClass(typeof(IAppliableContracts))]
  public interface IAppliable
  {
    public virtual int ContentHash => FunctionName.GetDeterministicHashCode();
    
    string /*!*/ FunctionName { get; }

    /// <summary>
    /// Emits to "stream" the operator applied to the given arguments.
    /// The length of "args" can be anything that the parser allows for this appliable operator
    /// (but can be nothing else).
    /// </summary>
    /// <param name="args"></param>
    /// <param name="stream"></param>
    /// <param name="contextBindingStrength"></param>
    /// <param name="fragileContext"></param>
    void Emit(IList<Expr> /*!*/ args, TokenTextWriter /*!*/ stream, int contextBindingStrength, bool fragileContext);

    void Resolve(ResolutionContext /*!*/ rc, Expr /*!*/ subjectForErrorReporting);

    /// <summary>
    /// Requires the object to have been properly resolved.
    /// </summary>
    int ArgumentCount { get; }

    /// <summary>
    /// Typechecks the arguments "args" for the Appliable.  If the arguments are
    /// appropriate, returns the result type; otherwise returns null.
    /// As result of the type checking, the values of type parameters of the
    /// appliable can be returned (which are then stored in the NAryExpr and later
    /// also used in the VCExprAST).
    /// Requires the object to have been successfully resolved.
    /// Requires args.Length == ArgumentCount.
    /// Requires all elements of "args" to have a non-null Type field.
    /// </summary>
    /// <param name="args"></param>
    /// <param name="tc"></param>
    Type Typecheck(IList<Expr> /*!*/ args, out TypeParamInstantiation /*!*/ tpInstantiation,
      TypecheckingContext /*!*/ tc);

    // Contract.Requires( Microsoft.SpecSharp.Collections.Reductions.Forall{Expr! arg in args; arg.Type != null});

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    Type /*!*/ ShallowType(IList<Expr> /*!*/ args);

    T Dispatch<T>(IAppliableVisitor<T> /*!*/ visitor);
  }

  [ContractClassFor(typeof(IAppliable))]
  abstract class IAppliableContracts : IAppliable
  {
    #region IAppliable Members

    public string FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();
      }
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      Contract.Requires(args != null);
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      Contract.Requires(rc != null);
      Contract.Requires(subjectForErrorReporting != null);
      throw new NotImplementedException();
    }

    public int ArgumentCount
    {
      get { throw new NotImplementedException(); }
    }

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      Contract.Requires(args != null);
      Contract.Requires(tc != null);
      Contract.Ensures(Contract.ValueAtReturn(out args) != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(args.Count == Contract.OldValue(args.Count));
      throw new NotImplementedException();
    }

    public Type ShallowType(IList<Expr> args)
    {
      Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      Contract.Requires(visitor != null);
      throw new NotImplementedException();
    }

    #endregion
  }


  [ContractClass(typeof(IOverloadedAppliableContracts))]
  public interface IOverloadedAppliable
  {
    void ResolveOverloading(NAryExpr /*!*/ expr);
    bool DoNotResolveOverloading { get; set; }
  }

  [ContractClassFor(typeof(IOverloadedAppliable))]
  public abstract class IOverloadedAppliableContracts : IOverloadedAppliable
  {
    #region IOverloadedAppliable Members

    void IOverloadedAppliable.ResolveOverloading(NAryExpr expr)
    {
      Contract.Requires(expr != null);
      throw new NotImplementedException();
    }

    public bool DoNotResolveOverloading
    {
      get { throw new NotImplementedException(); }
      set { throw new NotImplementedException(); }
    }

    #endregion
  }

  public class UnaryOperator : IAppliable
  {
    private IToken /*!*/
      tok;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(tok != null);
    }

    public enum Opcode
    {
      Neg,
      Not
    }

    private Opcode op;

    public Opcode Op
    {
      get { return op; }
    }

    public UnaryOperator(IToken tok, Opcode op)
    {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.op = op;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is UnaryOperator))
      {
        return false;
      }

      UnaryOperator other = (UnaryOperator) obj;
      return object.Equals(this.op, other.op);
    }

    [Pure]
    public override int GetHashCode()
    {
      return (int) this.op;
    }

    public string /*!*/ FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);

        switch (this.op)
        {
          case Opcode.Neg:
            return "-";
          case Opcode.Not:
            return "!";
        }

        System.Diagnostics.Debug.Fail("unknown unary operator: " + op.ToString());
        throw new Exception();
      }
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.SetToken(ref this.tok);
      Contract.Assert(args.Count == 1);
      // determine if parens are needed
      int opBindingStrength = 0x70;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded)
      {
        stream.Write("(");
      }

      stream.Write(FunctionName);
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      if (parensNeeded)
      {
        stream.Write(")");
      }
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      if (rc.TriggerMode && this.op == Opcode.Not)
      {
        rc.Error(subjectForErrorReporting, "boolean operators are not allowed in triggers");
      }
    }

    public int ArgumentCount
    {
      get { return 1; }
    }

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(Contract.ValueAtReturn(out args) != null);

      Contract.Assume(args.Count == 1);
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      Type arg0type = cce.NonNull(cce.NonNull(args[0]).Type);
      switch (this.op)
      {
        case Opcode.Neg:
          if (arg0type.Unify(Type.Int))
          {
            return Type.Int;
          }

          if (arg0type.Unify(Type.Real))
          {
            return Type.Real;
          }

          //if (arg0type.Unify(Type.Float)) {
          //return Type.Float;
          //}
          goto BAD_TYPE;
        case Opcode.Not:
          if (arg0type.Unify(Type.Bool))
          {
            return Type.Bool;
          }

          goto BAD_TYPE;
      }

      System.Diagnostics.Debug.Fail("unknown unary operator: " + op.ToString());
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
      BAD_TYPE:
      tc.Error(this.tok, "invalid argument type ({1}) to unary operator {0}",
        this.FunctionName, arg0type);
      return null;
    }

    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      switch (this.op)
      {
        case Opcode.Neg:
          return cce.NonNull(cce.NonNull(args[0]).Type);
        case Opcode.Not:
          return Type.Bool;
        default:
        {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        } // unexpected unary operator
      }
    }

    public object Evaluate(object argument)
    {
      if (argument == null)
      {
        return null;
      }

      switch (this.op)
      {
        case Opcode.Neg:
          if (argument is BigNum)
          {
            return -((BigNum) argument);
          }

          if (argument is BigDec)
          {
            return -((BigDec) argument);
          }

          if (argument is BigFloat)
          {
            return -((BigFloat) argument);
          }

          break;
        case Opcode.Not:
          if (argument is bool)
          {
            return !((bool) argument);
          }

          throw new System.InvalidOperationException("unary Not only applies to bool");
      }

      return null; // unreachable
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class BinaryOperator : IAppliable, IOverloadedAppliable
  {
    private IToken /*!*/
      tok;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(tok != null);
    }

    public bool DoNotResolveOverloading { get; set; }

    public enum Opcode
    {
      Add,
      Sub,
      Mul,
      Div,
      Mod,
      RealDiv,
      FloatDiv,
      Pow,
      Eq,
      Neq,
      Gt,
      Ge,
      Lt,
      Le,
      And,
      Or,
      Imp,
      Iff
    }

    private Opcode op;

    public Opcode Op
    {
      get { return op; }
    }

    public BinaryOperator(IToken tok, Opcode op)
    {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.op = op;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is BinaryOperator))
      {
        return false;
      }

      BinaryOperator other = (BinaryOperator) obj;
      return object.Equals(this.op, other.op);
    }

    [Pure]
    public override int GetHashCode()
    {
      return (int) this.op << 1;
    }

    public string /*!*/ FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);

        switch (this.op)
        {
          case Opcode.Add:
            return "+";
          case Opcode.Sub:
            return "-";
          case Opcode.Mul:
            return "*";
          case Opcode.Div:
            return "div";
          case Opcode.Mod:
            return "mod";
          case Opcode.RealDiv:
            return "/";
          case Opcode.Pow:
            return "**";
          case Opcode.Eq:
            return "==";
          case Opcode.Neq:
            return "!=";
          case Opcode.Gt:
            return ">";
          case Opcode.Ge:
            return ">=";
          case Opcode.Lt:
            return "<";
          case Opcode.Le:
            return "<=";
          case Opcode.And:
            return "&&";
          case Opcode.Or:
            return "||";
          case Opcode.Imp:
            return "==>";
          case Opcode.Iff:
            return "<==>";
        }

        System.Diagnostics.Debug.Fail("unknown binary operator: " + op.ToString());
        throw new Exception();
      }
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.SetToken(ref this.tok);
      Contract.Assert(args.Count == 2);
      // determine if parens are needed
      int opBindingStrength;
      bool fragileLeftContext = false; // false means "allow same binding power on left without parens"
      bool fragileRightContext = false; // false means "allow same binding power on right without parens"
      switch (this.op)
      {
        case Opcode.Add:
          opBindingStrength = 0x40;
          break;
        case Opcode.Sub:
          opBindingStrength = 0x40;
          fragileRightContext = true;
          break;
        case Opcode.Mul:
          opBindingStrength = 0x50;
          break;
        case Opcode.Div:
          opBindingStrength = 0x50;
          fragileRightContext = true;
          break;
        case Opcode.Mod:
          opBindingStrength = 0x50;
          fragileRightContext = true;
          break;
        case Opcode.RealDiv:
          opBindingStrength = 0x50;
          fragileRightContext = true;
          break;
        case Opcode.Pow:
          opBindingStrength = 0x60;
          fragileRightContext = true;
          break;
        case Opcode.Eq:
        case Opcode.Neq:
        case Opcode.Gt:
        case Opcode.Ge:
        case Opcode.Lt:
        case Opcode.Le:
          opBindingStrength = 0x30;
          fragileLeftContext = fragileRightContext = true;
          break;
        case Opcode.And:
          opBindingStrength = 0x20;
          break;
        case Opcode.Or:
          opBindingStrength = 0x21;
          break;
        case Opcode.Imp:
          opBindingStrength = 0x10;
          fragileLeftContext = true;
          break;
        case Opcode.Iff:
          opBindingStrength = 0x00;
          break;
        default:
          System.Diagnostics.Debug.Fail("unknown binary operator: " + op.ToString());
          opBindingStrength =
            -1; // to please compiler, which refuses to consider whether or not all enumeration cases have been considered!
          break;
      }

      int opBS = opBindingStrength & 0xF0;
      int ctxtBS = contextBindingStrength & 0xF0;
      bool parensNeeded = opBS < ctxtBS ||
                          (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

      var pop = stream.push(FunctionName);
      if (parensNeeded)
      {
        stream.Write("(");
      }

      cce.NonNull(args[0]).Emit(stream, opBindingStrength, fragileLeftContext);
      stream.sep();
      stream.Write(" {0} ", FunctionName);
      cce.NonNull(args[1]).Emit(stream, opBindingStrength, fragileRightContext);
      if (parensNeeded)
      {
        stream.Write(")");
      }

      stream.pop(pop);
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      if (rc.TriggerMode)
      {
        switch (this.op)
        {
          case Opcode.Add:
          case Opcode.Sub:
          case Opcode.Mul:
          case Opcode.Div:
          case Opcode.Mod:
          case Opcode.RealDiv:
          case Opcode.Pow:
          case Opcode.Neq: // Neq is allowed, but not Eq
            break;

          case Opcode.Eq:
            rc.Error(subjectForErrorReporting, "equality is not allowed in triggers");
            break;

          case Opcode.Gt:
          case Opcode.Ge:
          case Opcode.Lt:
          case Opcode.Le:
            rc.Error(subjectForErrorReporting, "arithmetic comparisons are not allowed in triggers");
            break;

          case Opcode.And:
          case Opcode.Or:
          case Opcode.Imp:
          case Opcode.Iff:
            rc.Error(subjectForErrorReporting, "boolean operators are not allowed in triggers");
            break;

          default:
            System.Diagnostics.Debug.Fail("unknown binary operator: " + this.op.ToString());
            break;
        }
      }
    }

    public int ArgumentCount
    {
      get { return 2; }
    }

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(args != null);
      Contract.Assert(args.Count == 2);
      // the default; the only binary operator with a type parameter is equality, but right
      // we don't store this parameter because it does not appear necessary
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      Expr arg0 = cce.NonNull(args[0]);
      Expr arg1 = cce.NonNull(args[1]);
      Type arg0type = cce.NonNull(arg0.Type);
      Type arg1type = cce.NonNull(arg1.Type);
      switch (this.op)
      {
        case Opcode.Add:
        case Opcode.Sub:
        case Opcode.Mul:
          if (arg0type.Unify(Type.Int) && arg1type.Unify(Type.Int))
          {
            return Type.Int;
          }

          if (arg0type.Unify(Type.Real) && arg1type.Unify(Type.Real))
          {
            return Type.Real;
          }

          if (arg0type.IsFloat && arg1type.IsFloat)
          {
            if (arg0type.FloatExponent == arg1type.FloatExponent &&
                arg0type.FloatSignificand == arg1type.FloatSignificand)
            {
              //So we never call arg0type.Unify, but it should be ok
              return Type.GetFloatType(arg0type.FloatSignificand, arg0type.FloatExponent);
            }
          }

          goto BAD_TYPE;
        case Opcode.Div:
        case Opcode.Mod:
          if (arg0type.Unify(Type.Int) && arg1type.Unify(Type.Int))
          {
            return Type.Int;
          }

          goto BAD_TYPE;
        case Opcode.RealDiv:
          if ((arg0type.Unify(Type.Int) || arg0type.Unify(Type.Real)) &&
              (arg1type.Unify(Type.Int) || arg1type.Unify(Type.Real)))
          {
            return Type.Real;
          }

          if (arg0type.IsFloat && arg1type.IsFloat)
          {
            if (arg0type.FloatExponent == arg1type.FloatExponent &&
                arg0type.FloatSignificand == arg1type.FloatSignificand)
            {
              //So we never call arg0type.Unify, but it should be ok
              return Type.GetFloatType(arg0type.FloatSignificand, arg0type.FloatExponent);
            }
          }

          goto BAD_TYPE;
        case Opcode.Pow:
          if (arg0type.Unify(Type.Real) && arg1type.Unify(Type.Real))
          {
            return Type.Real;
          }

          goto BAD_TYPE;
        case Opcode.Eq:
        case Opcode.Neq:
          // Comparison is allowed if the argument types are unifiable
          // (i.e., if there is any chance that the values of the arguments are
          // in the same domain)
          if (arg0type.Equals(arg1type))
          {
            // quick path
            return Type.Bool;
          }

          List<TypeVariable> /*!*/
            unifiable = new List<TypeVariable>();
          unifiable.AddRange(arg0type.FreeVariables);
          unifiable.AddRange(arg1type.FreeVariables);

          if (arg0type.Unify(arg1type, unifiable, new Dictionary<TypeVariable /*!*/, Type /*!*/>()))
          {
            return Type.Bool;
          }

          goto BAD_TYPE;
        case Opcode.Gt:
        case Opcode.Ge:
        case Opcode.Lt:
        case Opcode.Le:
          if (arg0type.Unify(Type.Int) && arg1type.Unify(Type.Int))
          {
            return Type.Bool;
          }

          if (arg0type.Unify(Type.Real) && arg1type.Unify(Type.Real))
          {
            return Type.Bool;
          }

          if (arg0type.IsFloat && arg1type.IsFloat)
          {
            if (arg0type.FloatExponent == arg1type.FloatExponent &&
                arg0type.FloatSignificand == arg1type.FloatSignificand)
            {
              return Type.Bool;
            }
          }

          goto BAD_TYPE;
        case Opcode.And:
        case Opcode.Or:
        case Opcode.Imp:
        case Opcode.Iff:
          if (arg0type.Unify(Type.Bool) && arg1type.Unify(Type.Bool))
          {
            return Type.Bool;
          }

          goto BAD_TYPE;
      }

      System.Diagnostics.Debug.Fail("unknown binary operator: " + op.ToString());
      {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
      BAD_TYPE:
      tc.Error(this.tok, "invalid argument types ({1} and {2}) to binary operator {0}", this.FunctionName, arg0type,
        arg1type);
      return null;
    }

    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      switch (this.op)
      {
        case Opcode.Add:
        case Opcode.Sub:
        case Opcode.Mul:
          return cce.NonNull(args[0]).ShallowType;

        case Opcode.Div:
        case Opcode.Mod:
          return Type.Int;

        case Opcode.RealDiv:
        case Opcode.Pow:
          return Type.Real;

        case Opcode.Eq:
        case Opcode.Neq:
        case Opcode.Gt:
        case Opcode.Ge:
        case Opcode.Lt:
        case Opcode.Le:
        case Opcode.And:
        case Opcode.Or:
        case Opcode.Imp:
        case Opcode.Iff:
          return Type.Bool;

        default:
        {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        } // unexpected binary operator
      }
    }

    public void ResolveOverloading(NAryExpr expr)
    {
      //Contract.Requires(expr != null);

      // immutable Expr must not be modified
      if (DoNotResolveOverloading || expr.Immutable)
      {
        return;
      }

      Expr arg0 = cce.NonNull(expr.Args[0]);
      Expr arg1 = cce.NonNull(expr.Args[1]);
      switch (op)
      {
        case Opcode.Eq:
          if (arg0.Type != null && arg0.Type.IsBool && arg1.Type != null && arg1.Type.IsBool)
          {
            expr.Fun = new BinaryOperator(tok, Opcode.Iff);
          }

          break;
        case Opcode.Neq:
          if (arg0.Type != null && arg0.Type.IsBool && arg1.Type != null && arg1.Type.IsBool)
          {
            expr.Fun = new BinaryOperator(tok, Opcode.Iff);
            var arg1New = new NAryExpr(expr.tok, new UnaryOperator(tok, UnaryOperator.Opcode.Not),
              new List<Expr> {arg1});

            // ugly ... there should be some more general approach,
            // e.g., to typecheck the whole expression again
            arg1New.Type = Type.Bool;
            arg1New.TypeParameters = SimpleTypeParamInstantiation.EMPTY;

            expr.Args[1] = arg1New;
          }

          break;
      }
    }

    public object Evaluate(object e1, object e2)
    {
      if (e1 == null || e2 == null)
      {
        return null;
      }

      switch (this.op)
      {
        case Opcode.Add:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) + ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) + ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) + ((BigFloat) e2);
          }

          break;
        case Opcode.Sub:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) - ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) - ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) - ((BigFloat) e2);
          }

          break;
        case Opcode.Mul:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) * ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) * ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) * ((BigFloat) e2);
          }

          break;
        case Opcode.Div:
          if (e1 is BigNum && e2 is BigNum)
          {
            return /* TODO: right semantics? */ ((BigNum) e1) / ((BigNum) e2);
          }

          break;
        case Opcode.Mod:
          if (e1 is BigNum && e2 is BigNum)
          {
            return /* TODO: right semantics? */ ((BigNum) e1) % ((BigNum) e2);
          }

          break;
        case Opcode.RealDiv:
          // TODO: add partial evaluation fro real division
          break;
        case Opcode.FloatDiv:
          //TODO: add float division
          break;
        case Opcode.Pow:
          // TODO: add partial evaluation fro real exponentiation
          break;
        case Opcode.Lt:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) < ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) < ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) < ((BigFloat) e2);
          }

          break;
        case Opcode.Le:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) <= ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) <= ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) <= ((BigFloat) e2);
          }

          break;
        case Opcode.Gt:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) > ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) > ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) > ((BigFloat) e2);
          }

          break;
        case Opcode.Ge:
          if (e1 is BigNum && e2 is BigNum)
          {
            return ((BigNum) e1) >= ((BigNum) e2);
          }

          if (e1 is BigDec && e2 is BigDec)
          {
            return ((BigDec) e1) >= ((BigDec) e2);
          }

          if (e1 is BigFloat && e2 is BigFloat)
          {
            return ((BigFloat) e1) >= ((BigFloat) e2);
          }

          break;

        case Opcode.And:
          if (e1 is bool && e2 is bool)
          {
            return (bool) e1 && (bool) e2;
          }

          break;
        case Opcode.Or:
          if (e1 is bool && e2 is bool)
          {
            return (bool) e1 || (bool) e2;
          }

          break;
        case Opcode.Imp:
          if (e1 is bool && e2 is bool)
          {
            return !(bool) e1 || (bool) e2;
          }

          break;
        case Opcode.Iff:
          if (e1 is bool && e2 is bool)
          {
            return e1 == e2;
          }

          break;

        case Opcode.Eq:
          return Equals(e1, e2);
        case Opcode.Neq:
          return !Equals(e1, e2);
      }

      throw new System.InvalidOperationException("bad types to binary operator " + this.op);
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class TypeCoercion : IAppliable
  {
    private IToken /*!*/
      tok;

    public Type /*!*/
      Type;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(tok != null);
    }

    public TypeCoercion(IToken tok, Type type)
    {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      this.tok = tok;
      this.Type = type;
    }

    public override bool Equals(object obj)
    {
      TypeCoercion other = obj as TypeCoercion;
      if (other == null)
      {
        return false;
      }
      else
      {
        return object.Equals(Type, other.Type);
      }
    }

    public override int GetHashCode()
    {
      return Type.GetHashCode();
    }

    public
      string /*!*/ FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);

        return ":";
      }
    }

    public void Emit(IList<Expr> /*!*/ args, TokenTextWriter /*!*/ stream,
      int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(args != null);
      //Contract.Requires(stream != null);
      stream.SetToken(ref this.tok);
      Contract.Assert(args.Count == 1);
      // determine if parens are needed
      int opBindingStrength = 0x80;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded)
      {
        stream.Write("(");
      }

      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write("{0} ", FunctionName);
      Type.Emit(stream, 0);

      if (parensNeeded)
      {
        stream.Write(")");
      }
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      this.Type = this.Type.ResolveType(rc);
    }

    public int ArgumentCount
    {
      get { return 1; }
    }

    public Type Typecheck(IList<Expr> /*!*/ args,
      out TypeParamInstantiation /*!*/ tpInstantiation,
      TypecheckingContext /*!*/ tc)
    {
      //Contract.Requires(args != null);
      //Contract.Requires(tc != null);
      Contract.Ensures(args != null);

      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      Contract.Assume(args.Count == 1);
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;

      if (!this.Type.Unify(cce.NonNull(cce.NonNull(args[0]).Type)))
      {
        tc.Error(this.tok, "{0} cannot be coerced to {1}",
          cce.NonNull(args[0]).Type, this.Type);
      }

      return this.Type;
    }

    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.Type;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class ArithmeticCoercion : IAppliable
  {
    public enum CoercionType
    {
      ToInt,
      ToReal
    }

    private IToken /*!*/
      tok;

    public readonly CoercionType Coercion;
    private readonly string name;
    private readonly Type type;
    private readonly Type argType;
    private readonly int hashCode;

    public ArithmeticCoercion(IToken tok, CoercionType coercion)
    {
      this.tok = tok;
      this.Coercion = coercion;

      switch (coercion)
      {
        case CoercionType.ToInt:
          this.name = "int";
          this.type = Type.Int;
          this.argType = Type.Real;
          this.hashCode = 1;
          break;
        case CoercionType.ToReal:
          this.name = "real";
          this.type = Type.Real;
          this.argType = Type.Int;
          this.hashCode = 2;
          break;
        default:
          Contract.Assert(false);
          break;
      }
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.name;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object other)
    {
      ArithmeticCoercion ac = other as ArithmeticCoercion;
      return ac != null && this.Coercion == ac.Coercion;
    }

    [Pure]
    public override int GetHashCode()
    {
      return this.hashCode;
    }

    public string /*!*/ FunctionName
    {
      get { return this.name; }
    }

    public int ArgumentCount
    {
      get { return 1; }
    }

    virtual public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.Write(this.name);
      stream.Write("(");
      args.Emit(stream);
      stream.Write(")");
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
    }

    public virtual Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      Contract.Assert(args.Count == 1);

      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;

      if (!cce.NonNull(cce.NonNull(args[0]).Type).Unify(argType))
      {
        tc.Error(this.tok, "argument type {0} does not match expected type {1}", cce.NonNull(args[0]).Type,
          this.argType);
      }

      return this.type;
    }

    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.type;
    }

    public virtual T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class MapSelect : IAppliable
  {
    public readonly int Arity;

    private readonly IToken /*!*/
      tok;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(tok != null);
    }


    public MapSelect(IToken tok, int arity)
    {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.Arity = arity;
    }

    public string /*!*/ FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);

        return "MapSelect";
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (!(obj is MapSelect))
      {
        return false;
      }

      MapSelect other = (MapSelect) obj;
      return this.Arity == other.Arity;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Arity.GetHashCode() * 2823;
    }

    public void Emit(IList<Expr> /*!*/ args, TokenTextWriter /*!*/ stream,
      int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(args != null);
      //Contract.Requires(stream != null);
      Contract.Assume(args.Count == Arity + 1);
      Emit(args, stream, contextBindingStrength, fragileContext, false);
    }

    public static void Emit(IList<Expr> /*!*/ args, TokenTextWriter /*!*/ stream,
      int contextBindingStrength, bool fragileContext,
      bool withRhs)
    {
      Contract.Requires(args != null);
      Contract.Requires(stream != null);
      const int opBindingStrength = 0x90;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded)
      {
        stream.Write("(");
      }

      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write("[");

      string sep = "";
      int lastIndex = withRhs ? args.Count - 1 : args.Count;
      for (int i = 1; i < lastIndex; ++i)
      {
        stream.Write(sep);
        sep = ", ";
        cce.NonNull(args[i]).Emit(stream);
      }

      if (withRhs)
      {
        stream.Write(" := ");
        cce.NonNull(args.Last()).Emit(stream);
      }

      stream.Write("]");
      if (parensNeeded)
      {
        stream.Write(")");
      }
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      // PR: nothing?
    }

    public int ArgumentCount
    {
      get { return Arity + 1; }
    }

    // it is assumed that each of the arguments has already been typechecked
    public static Type Typecheck(Type /*!*/ mapType,
      // we just pass an Absy, because in
      // the AssignCmd maps can also be
      // represented by non-expressions
      Absy /*!*/ map,
      List<Expr> /*!*/ indexes,
      // the type parameters, in this context, are the parameters of the
      // potentially polymorphic map type. Because it might happen that
      // the whole map type is unknown and represented using a MapTypeProxy,
      // the instantiations given in the following out-parameter are subject
      // to change if further unifications are done.
      out TypeParamInstantiation /*!*/ tpInstantiation,
      TypecheckingContext /*!*/ tc,
      IToken /*!*/ typeCheckingSubject,
      string /*!*/ opName)
    {
      Contract.Requires(mapType != null);
      Contract.Requires(map != null);
      Contract.Requires(indexes != null);
      Contract.Requires(tc != null);
      Contract.Requires(typeCheckingSubject != null);
      Contract.Requires(opName != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      mapType = mapType.Expanded;
      if (mapType.IsMap && mapType.MapArity != indexes.Count)
      {
        tc.Error(typeCheckingSubject, "wrong number of arguments in {0}: {1} instead of {2}",
          opName, indexes.Count, mapType.MapArity);
        tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
        return null;
      }
      else if (!mapType.Unify(new MapTypeProxy(map.tok, "select", indexes.Count)))
      {
        tc.Error(map.tok, "{0} applied to a non-map: {1}", opName, map);
        tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
        return null;
      }

      mapType = TypeProxy.FollowProxy(mapType);

      if (mapType is MapType)
      {
        MapType mt = (MapType) mapType;
        return mt.CheckArgumentTypes(indexes, out tpInstantiation,
          typeCheckingSubject, opName, tc);
      }
      else
      {
        MapTypeProxy mt = (MapTypeProxy) mapType;
        return mt.CheckArgumentTypes(indexes, out tpInstantiation,
          typeCheckingSubject, opName, tc);
      }
    }

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Assume(args.Count == Arity + 1);

      // FIXME: Wny are we passing a copy?
      List<Expr> actualArgs = new List<Expr>();
      for (int i = 1; i < args.Count; ++i)
      {
        actualArgs.Add(args[i]);
      }

      return Typecheck(cce.NonNull(cce.NonNull(args[0]).Type), cce.NonNull(args[0]),
        actualArgs, out tpInstantiation, tc, this.tok, "map select");
    }

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Expr a0 = cce.NonNull(args[0]);
      Type a0Type = a0.ShallowType;
      if (a0Type == null || !a0Type.IsMap)
      {
        // we are unable to determine the type of the select, so just return an arbitrary type
        return Type.Int;
      }

      MapType mapType = a0Type.AsMap;
      List<Type> actualArgTypes = new List<Type>();
      for (int i = 1; i < args.Count; ++i)
      {
        actualArgTypes.Add(cce.NonNull(args[i]).ShallowType);
      }

      return Type.InferValueType(mapType.TypeParameters, mapType.Arguments, mapType.Result, actualArgTypes);
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class MapStore : IAppliable
  {
    public readonly int Arity;

    public readonly IToken /*!*/
      tok;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(tok != null);
    }


    public MapStore(IToken tok, int arity)
    {
      Contract.Requires(tok != null);
      this.tok = tok;
      this.Arity = arity;
    }

    public string /*!*/ FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);

        return "MapStore";
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (!(obj is MapStore))
      {
        return false;
      }

      MapStore other = (MapStore) obj;
      return this.Arity == other.Arity;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Arity.GetHashCode() * 28231;
    }

    public void Emit(IList<Expr> /*!*/ args, TokenTextWriter /*!*/ stream,
      int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(args != null);
      //Contract.Requires(stream != null);
      Contract.Assert(args.Count == Arity + 2);
      MapSelect.Emit(args, stream, contextBindingStrength, fragileContext, true);
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      // PR: nothing?
    }

    public int ArgumentCount
    {
      get { return Arity + 2; }
    }

    // it is assumed that each of the arguments has already been typechecked
    public static Type Typecheck(IList<Expr> /*!*/ args, out TypeParamInstantiation /*!*/ tpInstantiation,
      TypecheckingContext /*!*/ tc,
      IToken /*!*/ typeCheckingSubject,
      string /*!*/ opName)
    {
      Contract.Requires(args != null);
      Contract.Requires(tc != null);
      Contract.Requires(typeCheckingSubject != null);
      Contract.Requires(opName != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);

      // part of the type checking works exactly as for MapSelect
      List<Expr> selectArgs = new List<Expr>();
      for (int i = 1; i < args.Count - 1; ++i)
      {
        selectArgs.Add(args[i]);
      }

      Type resultType =
        MapSelect.Typecheck(cce.NonNull(cce.NonNull(args[0]).Type), cce.NonNull(args[0]),
          selectArgs, out tpInstantiation, tc, typeCheckingSubject, opName);

      // check the the rhs has the right type
      if (resultType == null)
      {
        // error messages have already been created by MapSelect.Typecheck
        return null;
      }

      Type rhsType = cce.NonNull(cce.NonNull(args.Last()).Type);
      if (!resultType.Unify(rhsType))
      {
        tc.Error(cce.NonNull(args.Last()).tok,
          "right-hand side in {0} with wrong type: {1} (expected: {2})",
          opName, rhsType, resultType);
        return null;
      }

      return cce.NonNull(args[0]).Type;
    }

    public Type Typecheck(IList<Expr> /*!*/ args,
      out TypeParamInstantiation /*!*/ tpInstantiation,
      TypecheckingContext /*!*/ tc)
    {
      //Contract.Requires(args != null);
      //Contract.Requires(tc != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Ensures(Contract.ValueAtReturn(out args) != null);
      Contract.Assert(args.Count == Arity + 2);
      return Typecheck(args, out tpInstantiation, tc, this.tok, "map store");
    }

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return cce.NonNull(args[0]).ShallowType;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }


  public class IfThenElse : IAppliable
  {
    private IToken /*!*/
      _tok;

    public IToken /*!*/ tok
    {
      get
      {
        Contract.Ensures(Contract.Result<IToken>() != null);
        return this._tok;
      }
      set
      {
        Contract.Requires(value != null);
        this._tok = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._tok != null);
    }

    public IfThenElse(IToken tok)
    {
      Contract.Requires(tok != null);
      this._tok = tok;
    }

    public string /*!*/ FunctionName
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);

        return "if-then-else";
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (!(obj is IfThenElse))
      {
        return false;
      }

      return true;
    }

    [Pure]
    public override int GetHashCode()
    {
      return 1;
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      //Contract.Requires(args != null);
      stream.SetToken(this);
      Contract.Assert(args.Count == 3);
      stream.push();
      stream.Write("(if ");
      cce.NonNull(args[0]).Emit(stream, 0x00, false);
      stream.sep();
      stream.Write(" then ");
      cce.NonNull(args[1]).Emit(stream, 0x00, false);
      stream.sep();
      stream.Write(" else ");
      cce.NonNull(args[2]).Emit(stream, 0x00, false);
      stream.Write(")");
      stream.pop();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      //Contract.Requires(subjectForErrorReporting != null);
      //Contract.Requires(rc != null);
      // PR: nothing?
    }

    public int ArgumentCount
    {
      get { return 3; }
    }

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      //Contract.Requires(args != null);
      Contract.Ensures(args != null);
      Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
      Contract.Assert(args.Count == 3);
      // the default; the only binary operator with a type parameter is equality, but right
      // we don't store this parameter because it does not appear necessary
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      Expr arg0 = cce.NonNull(args[0]);
      Expr arg1 = cce.NonNull(args[1]);
      Expr arg2 = cce.NonNull(args[2]);

      if (!cce.NonNull(arg0.Type).Unify(Type.Bool))
      {
        tc.Error(this.tok, "the first argument to if-then-else should be bool, not {0}", arg0.Type);
      }
      else if (!cce.NonNull(arg1.Type).Unify(cce.NonNull(arg2.Type)))
      {
        tc.Error(this.tok, "branches of if-then-else have incompatible types {0} and {1}", arg1.Type, arg2.Type);
      }
      else
      {
        return arg1.Type;
      }

      return null;
    }

    /// <summary>
    /// Returns the result type of the IAppliable, supposing the argument are of the correct types.
    /// </summary>
    public Type ShallowType(IList<Expr> args)
    {
      //Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return cce.NonNull(args[1]).ShallowType;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this);
    }
  }

  public class FieldAccess : IAppliable
  {
    public IToken tok { get; set; }
    
    public string FieldName { get; }

    public DatatypeTypeCtorDecl DatatypeTypeCtorDecl { get; private set; }
    
    // each accessor is specified by a pair comprising a constructor index
    // and a selector index within the constructor corresponding to it
    public List<DatatypeAccessor> Accessors { get; private set; }

    public IEnumerable<Variable> Fields => Enumerable.Range(0, Accessors.Count).Select(i => Field(i));

    private DatatypeConstructor Constructor(int index)
    {
      var accessor = Accessors[index];
      return DatatypeTypeCtorDecl.Constructors[accessor.ConstructorIndex];
    }
    
    private Variable Field(int index)
    {
      var accessor = Accessors[index];
      return DatatypeTypeCtorDecl.Constructors[accessor.ConstructorIndex].InParams[accessor.FieldIndex];
    }

    public FieldAccess(IToken tok, string fieldName)
    {
      this.tok = tok;
      this.FieldName = fieldName;
    }
    
    public FieldAccess(IToken tok, string fieldName, DatatypeTypeCtorDecl datatypeTypeCtorDecl, List<DatatypeAccessor> accessors)
    {
      this.tok = tok;
      this.FieldName = fieldName;
      this.DatatypeTypeCtorDecl = datatypeTypeCtorDecl;
      this.Accessors = accessors;
    }

    public string FunctionName => "field-access";

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj is FieldAccess fieldAccess)
      {
        return DatatypeTypeCtorDecl.Equals(fieldAccess.DatatypeTypeCtorDecl) && Accessors.Equals(fieldAccess.Accessors);
      }
      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return 1;
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      const int opBindingStrength = 0x90;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);
      stream.SetToken(this);
      Contract.Assert(args.Count == 1);
      stream.push();
      if (parensNeeded)
      {
        stream.Write("(");
      }
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write("->{0}", FieldName);
      if (parensNeeded)
      {
        stream.Write(")");
      }
      stream.pop();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      // The work of resolution is delayed to type checking when the datatype is known.
    }

    public int ArgumentCount => 1;

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      Contract.Assert(args.Count == 1);
      return Typecheck(cce.NonNull(args[0]).Type, tc, out tpInstantiation);
    }
    
    public Type Typecheck(Type type, TypecheckingContext tc, out TypeParamInstantiation tpInstantiation)
    {
      type = TypeProxy.FollowProxy(type);
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      if (!(type.Expanded is CtorType ctorType))
      {
        tc.Error(this.tok, "field-access must be applied to a datatype, {0} is not a datatype", type);
        return null;
      }
      if (!(ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl))
      {
        tc.Error(this.tok, "field-access must be applied to a datatype, {0} is not a datatype", ctorType);
        return null;
      }
      DatatypeTypeCtorDecl = datatypeTypeCtorDecl;
      Accessors = datatypeTypeCtorDecl.GetAccessors(FieldName);
      if (Accessors == null)
      {
        tc.Error(this.tok, "datatype {0} does not have a field with name {1}", ctorType, FieldName);
        return null;
      }
      Contract.Assert(Accessors.Count > 0);
      tpInstantiation = SimpleTypeParamInstantiation.From(Constructor(0).TypeParameters, ctorType.Arguments);
      var typeSubst = Constructor(0).TypeParameters.Zip(ctorType.Arguments).ToDictionary(
          x => x.Item1, 
          x => x.Item2);
      return Field(0).TypedIdent.Type.Substitute(typeSubst);
    }

    public Type Type(CtorType ctorType)
    {
      var typeSubst = Constructor(0).TypeParameters.Zip(ctorType.Arguments).ToDictionary(
        x => x.Item1, 
        x => x.Item2);
      return Field(0).TypedIdent.Type.Substitute(typeSubst);
    }

    public Type ShallowType(IList<Expr> args)
    {
      return Field(0).TypedIdent.Type;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      return visitor.Visit(this);
    }

    public NAryExpr Select(IToken token, Expr record)
    {
      var expr = new NAryExpr(token, this, new List<Expr> { record });
      ResolveAndTypecheck(expr);
      return expr;
    }

    public NAryExpr Update(IToken token, Expr record, Expr rhs)
    {
      var expr = Update(token, record, rhs, 0);
      for (int i = 1; i < Accessors.Count; i++)
      {
        var constructor = Constructor(i);
        var condExpr = new NAryExpr(token,
          new IsConstructor(token, constructor.datatypeTypeCtorDecl, constructor.index), new Expr[] { record });
        var thenExpr = Update(token, record, rhs, i);
        expr = new NAryExpr(token, new IfThenElse(token), new Expr[] { condExpr, thenExpr, expr });
      }
      ResolveAndTypecheck(expr);
      return expr;
    }

    private NAryExpr Update(IToken token, Expr record, Expr rhs, int index)
    {
      var constructor = Constructor(index);
      var args = Enumerable.Range(0, constructor.InParams.Count).Select(x =>
      {
        if (x == Accessors[index].FieldIndex)
        {
          return rhs;
        }

        var fieldName = constructor.InParams[x].Name;
        var fieldAccess = new FieldAccess(tok, fieldName, DatatypeTypeCtorDecl, DatatypeTypeCtorDecl.GetAccessors(fieldName));
        return fieldAccess.Select(token, record);
      }).ToList();
      return new NAryExpr(token, new FunctionCall(Constructor(index)), args);
    }

    private void ResolveAndTypecheck(Expr expr)
    {
      expr.Resolve(new ResolutionContext(null, null));
      expr.Typecheck(new TypecheckingContext(null, null));
    }
  }

  public class FieldUpdate : IAppliable
  {
    public IToken tok
    {
      get => fieldAccess.tok;
      set => fieldAccess.tok = value;
    }

    public DatatypeTypeCtorDecl DatatypeTypeCtorDecl => fieldAccess.DatatypeTypeCtorDecl;

    public FieldAccess FieldAccess => fieldAccess;
    
    private FieldAccess fieldAccess;

    public FieldUpdate(IToken tok, string fieldName)
    {
      this.fieldAccess = new FieldAccess(tok, fieldName);
    }
    
    public FieldUpdate(FieldAccess fieldAccess)
    {
      this.fieldAccess = fieldAccess;
    }

    public string FunctionName => "field-update";

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj is FieldUpdate fieldUpdate)
      {
        return fieldAccess.Equals(fieldUpdate.fieldAccess);
      }
      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return 1;
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      const int opBindingStrength = 0x90;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);
      stream.SetToken(this);
      Contract.Assert(args.Count == 2);
      stream.push();
      if (parensNeeded)
      {
        stream.Write("(");
      }
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write("->({0} := ", fieldAccess.FieldName);
      cce.NonNull(args[1]).Emit(stream, opBindingStrength, false);
      stream.Write(")");
      if (parensNeeded)
      {
        stream.Write(")");
      }
      stream.pop();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      // The work of resolution is delayed to type checking when the datatype is known.
    }

    public int ArgumentCount => 2;

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      Contract.Assert(args.Count == 2);
      return Typecheck(cce.NonNull(args[0]).Type, cce.NonNull(args[1]).Type, tc, out tpInstantiation);
    }
    
    public Type Typecheck(Type datatype, Type fieldType, TypecheckingContext tc, out TypeParamInstantiation tpInstantiation)
    {
      var expectedFieldType = fieldAccess.Typecheck(datatype, tc, out tpInstantiation);
      if (expectedFieldType == null)
      {
        return null;
      }
      if (!fieldType.Unify(expectedFieldType))
      {
        tc.Error(this.tok,
          $"right-hand side in field update with wrong type: {fieldType} (expected: {expectedFieldType})");
        return null;
      }
      return datatype;
    }

    public Type ShallowType(IList<Expr> args)
    {
      return args[0].Type;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      return visitor.Visit(this);
    }
    
    public NAryExpr Update(IToken token, Expr record, Expr rhs)
    {
      return fieldAccess.Update(token, record, rhs);
    }
  }
  
  public class IsConstructor : IAppliable
  {
    public IToken tok { get; set; }
    
    public string ConstructorName { get; }
    
    public DatatypeTypeCtorDecl DatatypeTypeCtorDecl { get; private set; }
    
    public int ConstructorIndex { get; private set; }
    
    public IsConstructor(IToken tok, string constructorName)
    {
      this.tok = tok;
      this.ConstructorName = constructorName;
    }
    
    public IsConstructor(IToken tok, DatatypeTypeCtorDecl datatypeTypeCtorDecl, int constructorIndex)
    {
      this.tok = tok;
      this.DatatypeTypeCtorDecl = datatypeTypeCtorDecl;
      this.ConstructorIndex = constructorIndex;
      this.ConstructorName = datatypeTypeCtorDecl.Constructors[constructorIndex].Name;
    }

    public string FunctionName => "is-constructor";

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj is IsConstructor isConstructor)
      {
        return DatatypeTypeCtorDecl.Equals(isConstructor.DatatypeTypeCtorDecl) &&
               ConstructorIndex == isConstructor.ConstructorIndex;
      }
      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return 1;
    }

    public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      const int opBindingStrength = 0x68;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);
      stream.SetToken(this);
      Contract.Assert(args.Count == 1);
      stream.push();
      if (parensNeeded)
      {
        stream.Write("(");
      }
      cce.NonNull(args[0]).Emit(stream, opBindingStrength, false);
      stream.Write(" is {0}", ConstructorName);
      if (parensNeeded)
      {
        stream.Write(")");
      }
      stream.pop();
    }

    public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
    {
      // The work of resolution is delayed to type checking when the datatype is known.
    }

    public int ArgumentCount => 1;

    public Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
    {
      Contract.Assert(args.Count == 1);
      return Typecheck(cce.NonNull(args[0]).Type, tc, out tpInstantiation);
    }
    
    public Type Typecheck(Type type, TypecheckingContext tc, out TypeParamInstantiation tpInstantiation)
    {
      type = TypeProxy.FollowProxy(type);
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      if (!(type.Expanded is CtorType ctorType))
      {
        tc.Error(this.tok, "is-constructor must be applied to a datatype, {0} is not a datatype", type);
        return null;
      }
      if (!(ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl))
      {
        tc.Error(this.tok, "is-constructor must be applied to a datatype, {0} is not a datatype", ctorType);
        return null;
      }
      DatatypeTypeCtorDecl = datatypeTypeCtorDecl;
      var constructor = datatypeTypeCtorDecl.GetConstructor(ConstructorName);
      if (constructor == null)
      {
        tc.Error(this.tok, "datatype {0} does not have a constructor with name {1}", ctorType, ConstructorName);
        return null;
      }
      ConstructorIndex = constructor.index;
      tpInstantiation = SimpleTypeParamInstantiation.From(constructor.TypeParameters, ctorType.Arguments);
      return Type.Bool;
    }

    public Type ShallowType(IList<Expr> args)
    {
      return Type.Bool;
    }

    public T Dispatch<T>(IAppliableVisitor<T> visitor)
    {
      return visitor.Visit(this);
    }
  }

  public class CodeExpr : Expr
  {
    public List<Variable> /*!*/
      LocVars;

    [Rep] public List<Block /*!*/> /*!*/ Blocks;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(LocVars != null);
      Contract.Invariant(cce.NonNullElements(Blocks));
    }

    public CodeExpr(List<Variable> /*!*/ localVariables, List<Block /*!*/> /*!*/ blocks, bool immutable = false)
      : base(Token.NoToken, immutable)
    {
      Contract.Requires(localVariables != null);
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Requires(0 < blocks.Count);
      LocVars = localVariables;
      Blocks = blocks;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    // FIXME: This seems wrong we don't want reference equality, we want structural equality
    [Pure]
    public override bool Equals(object obj)
    {
      return base.Equals(obj);
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

    public override int ContentHash => throw new NotImplementedException();

    [Pure]
    public override int ComputeHashCode()
    {
      return base.GetHashCode();
    }


    public override void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      //Contract.Requires(freeVars != null);
      // Treat a BlockEexpr as if it has no free variables at all
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      //level++;
      int level = 0;
      stream.WriteLine(level, "|{");

      if (this.LocVars.Count > 0)
      {
        stream.Write(level + 1, "var ");
        this.LocVars.Emit(stream, true);
        stream.WriteLine(";");
      }

      foreach (Block /*!*/ b in this.Blocks)
      {
        Contract.Assert(b != null);
        b.Emit(stream, level + 1);
      }

      stream.WriteLine();
      stream.WriteLine(level, "}|");

      stream.WriteLine();
      stream.WriteLine();
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);

      rc.PushVarContext();
      foreach (Variable /*!*/ v in LocVars)
      {
        Contract.Assert(v != null);
        v.Register(rc);
        v.Resolve(rc);
      }

      foreach (Variable /*!*/ v in LocVars)
      {
        Contract.Assert(v != null);
        v.ResolveWhere(rc);
      }

      rc.PushProcedureContext();
      foreach (Block /*!*/ b in Blocks)
      {
        Contract.Assert(b != null);
        b.Register(rc);
      }

      foreach (Block /*!*/ b in Blocks)
      {
        Contract.Assert(b != null);
        b.Resolve(rc);
      }

      rc.PopProcedureContext();
      rc.PopVarContext();
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (Variable /*!*/ v in LocVars)
      {
        Contract.Assert(v != null);
        v.Typecheck(tc);
      }

      foreach (Block /*!*/ b in Blocks)
      {
        Contract.Assert(b != null);
        b.Typecheck(tc);
      }

      this.Type = Type.Bool;
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Type.Bool;
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitCodeExpr(this);
    }
  }

  public class BvExtractExpr : Expr
  {
    public override int ContentHash => Util.GetHashCode(1947706825, Start, End, Bitvector.ContentHash);

    private /*readonly--except in StandardVisitor*/ Expr /*!*/
      _Bitvector;

    public Expr Bitvector
    {
      get { return _Bitvector; }
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Cannot change BitVector field of an immutable BvExtractExpr");
        }

        _Bitvector = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(_Bitvector != null);
    }

    public readonly int Start, End;

    public BvExtractExpr(IToken /*!*/ tok, Expr /*!*/ bv, int end, int start, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(bv != null);
      _Bitvector = bv;
      Start = start;
      End = end;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is BvExtractExpr))
      {
        return false;
      }

      BvExtractExpr other = (BvExtractExpr) obj;
      return object.Equals(this.Bitvector, other.Bitvector) &&
             this.Start.Equals(other.Start) && this.End.Equals(other.End);
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
      int h = this.Bitvector.GetHashCode();
      h ^= Start * 17 ^ End * 13;
      return h;
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      int opBindingStrength = 0x90;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded)
      {
        stream.Write("(");
      }

      Bitvector.Emit(stream, opBindingStrength, false);
      stream.Write("[" + End + ":" + Start + "]");
      if (parensNeeded)
      {
        stream.Write(")");
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Bitvector.Resolve(rc);
    }

    public override void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      //Contract.Requires(freeVars != null);
      Bitvector.ComputeFreeVariables(freeVars);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      Bitvector.Typecheck(tc);
      Contract.Assert(Bitvector.Type != null); // follows from postcondition of Expr.Typecheck

      if (Start < 0)
      {
        tc.Error(this, "start index in extract must not be negative");
      }
      else if (End < 0)
      {
        tc.Error(this, "end index in extract must not be negative");
      }
      else if (End < Start)
      {
        tc.Error(this, "start index in extract must be no bigger than the end index");
      }
      else
      {
        Type typeConstraint = new BvTypeProxy(this.tok, "extract", End - Start);
        if (typeConstraint.Unify(Bitvector.Type))
        {
          Type = Type.GetBvType(End - Start);
        }
        else
        {
          tc.Error(this, "extract operand must be a bitvector of at least {0} bits (got {1})", End - Start,
            Bitvector.Type);
        }
      }

      if (Type == null)
      {
        Type = new TypeProxy(this.tok, "type_checking_error");
      }
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Type.GetBvType(End - Start);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBvExtractExpr(this);
    }
  }

  public class BvConcatExpr : Expr
  {
    public override int ContentHash => Util.GetHashCode(1653318336, E0.ContentHash, E1.ContentHash);
    
    private /*readonly--except in StandardVisitor*/ Expr /*!*/
      _E0, _E1;

    public Expr E0
    {
      get => _E0;
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Can't change E0 reference on immutable Expr");
        }

        _E0 = value;
      }
    }

    public Expr E1
    {
      get => _E1;
      set
      {
        if (Immutable)
        {
          throw new InvalidOperationException("Can't change E1 reference on immutable Expr");
        }

        _E1 = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(E0 != null);
      Contract.Invariant(E1 != null);
    }


    public BvConcatExpr(IToken /*!*/ tok, Expr /*!*/ e0, Expr /*!*/ e1, bool immutable = false)
      : base(tok, immutable)
    {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      _E0 = e0;
      _E1 = e1;
      if (immutable)
      {
        CachedHashCode = ComputeHashCode();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object obj)
    {
      if (obj == null)
      {
        return false;
      }

      if (!(obj is BvConcatExpr))
      {
        return false;
      }

      BvConcatExpr other = (BvConcatExpr) obj;
      return object.Equals(this.E0, other.E0) && object.Equals(this.E1, other.E1);
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
      int h = this.E0.GetHashCode() ^ this.E1.GetHashCode() * 17;
      return h;
    }

    public override void Emit(TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
    {
      //Contract.Requires(stream != null);
      stream.SetToken(this);
      int opBindingStrength = 0x32;
      bool parensNeeded = opBindingStrength < contextBindingStrength ||
                          (fragileContext && opBindingStrength == contextBindingStrength);

      if (parensNeeded)
      {
        stream.Write("(");
      }

      E0.Emit(stream, opBindingStrength, false);
      stream.Write(" ++ ");
      // while this operator is associative, our incomplete axioms in int translation don't
      // make much use of it, so better stick to the actual tree shape
      E1.Emit(stream, opBindingStrength, true);
      if (parensNeeded)
      {
        stream.Write(")");
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      E0.Resolve(rc);
      E1.Resolve(rc);
    }

    public override void ComputeFreeVariables(Set /*Variable*/ freeVars)
    {
      //Contract.Requires(freeVars != null);
      E0.ComputeFreeVariables(freeVars);
      E1.ComputeFreeVariables(freeVars);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      E0.Typecheck(tc);
      Contract.Assert(E0.Type != null); // follows from postcondition of Expr.Typecheck
      E1.Typecheck(tc);
      Contract.Assert(E1.Type != null); // follows from postcondition of Expr.Typecheck

      if (E0.Type.Unify(new BvTypeProxy(this.tok, "concat0", 0)) &&
          E1.Type.Unify(new BvTypeProxy(this.tok, "concat1", 0)))
      {
        Type = new BvTypeProxy(this.tok, "concat", E0.Type, E1.Type);
      }
      else
      {
        tc.Error(this, "++ operands need to be bitvectors (got {0}, {1})", E0.Type, E1.Type);
      }

      if (Type == null)
      {
        Type = new TypeProxy(this.tok, "type_checking_error");
      }
    }

    public override Type /*!*/ ShallowType
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        Type t0 = E0.ShallowType;
        Type t1 = E1.ShallowType;
        int len0 = t0.IsBv ? t0.BvBits : /*expression is not type correct, so just pick an arbitrary number of bits*/0;
        int len1 = t1.IsBv ? t1.BvBits : /*expression is not type correct, so just pick an arbitrary number of bits*/0;
        return Type.GetBvType(len0 + len1);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitBvConcatExpr(this);
    }
  }
}
