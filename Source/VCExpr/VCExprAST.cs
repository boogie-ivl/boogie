using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;

// Prover-independent syntax trees for representing verification conditions
// The language can be seen as a simple polymorphically typed first-order logic,
// very similar to the expression language of Boogie

namespace Microsoft.Boogie.VCExprAST
{
  public class HelperFuns
  {
    public static bool SameElements(IEnumerable a, IEnumerable b)
    {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      IEnumerator ia = a.GetEnumerator();
      IEnumerator ib = b.GetEnumerator();
      while (true)
      {
        if (ia.MoveNext())
        {
          if (ib.MoveNext())
          {
            if (!Cce.NonNull(ia.Current).Equals(ib.Current))
            {
              return false;
            }
          }
          else
          {
            return false;
          }
        }
        else
        {
          return !ib.MoveNext();
        }
      }
    }

    public static int PolyHash(int init, int factor, IEnumerable a)
    {
      Contract.Requires(a != null);
      int res = init;
      foreach (object x in a)
      {
        res = res * factor + (Cce.NonNull(x)).GetHashCode();
      }

      return res;
    }

    public static List<T> ToList<T>(IEnumerable<T> l)
    {
      Contract.Requires(l != null);
      Contract.Ensures(Contract.Result<List<T>>() != null);
      List<T> /*!*/
        res = new List<T>();
      foreach (T x in l)
      {
        res.Add(x);
      }

      return res;
    }

    public static List<Type> ToTypeSeq(VCExpr[] exprs, int startIndex)
    {
      Contract.Requires(exprs != null);
      Contract.Requires((Contract.ForAll(0, exprs.Length, i => exprs[i] != null)));
      Contract.Ensures(Contract.Result<List<Type>>() != null);
      List<Type> /*!*/
        res = new List<Type>();
      for (int i = startIndex; i < exprs.Length; ++i)
      {
        res.Add(Cce.NonNull(exprs[i]).Type);
      }

      return res;
    }

    public static List<T /*!*/> /*!*/ ToNonNullList<T>(params T[] args) where T : class
    {
      Contract.Requires(args != null);
      List<T /*!*/> /*!*/
        res = new List<T>(args.Length);
      foreach (T t in args)
      {
        res.Add(Cce.NonNull(t));
      }

      return res;
    }

    public static IDictionary<A, B> Clone<A, B>(IDictionary<A, B> dict)
    {
      Contract.Requires(dict != null);
      Contract.Ensures(Contract.Result<IDictionary<A, B>>() != null);
      IDictionary<A, B> res = new Dictionary<A, B>(dict.Count);
      foreach (KeyValuePair<A, B> pair in dict)
      {
        res.Add(pair);
      }

      return res;
    }
  }

  [ContractClassFor(typeof(VCExpr))]
  public abstract class VCExprContracts : VCExpr
  {
    public override Type Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();
      }
    }

    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg)
    {
      Contract.Requires(visitor != null);
      throw new NotImplementedException();
    }
  }

  [ContractClass(typeof(VCExprContracts))]
  public abstract class VCExpr
  {
    public abstract Type Type { get; }

    public abstract Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg);

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      StringWriter sw = new StringWriter();
      VCExprPrinter printer = new VCExprPrinter(PrintOptions.Default);
      printer.Print(this, sw);
      return Cce.NonNull(sw.ToString());
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Literal expressions

  public class VCExprLiteral : VCExpr
  {
    private readonly Type LitType;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(LitType != null);
    }

    public override Type Type
    {
      get { return LitType; }
    }

    internal VCExprLiteral(Type type)
    {
      Contract.Requires(type != null);
      this.LitType = type;
    }

    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }

  public class VCExprIntLit : VCExprLiteral
  {
    public readonly BigNum Val;

    internal VCExprIntLit(BigNum val)
      : base(Type.Int)
    {
      this.Val = val;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprIntLit)
      {
        return Val == ((VCExprIntLit) that).Val;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprRealLit : VCExprLiteral
  {
    public readonly BigDec Val;

    internal VCExprRealLit(BigDec val)
      : base(Type.Real)
    {
      this.Val = val;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprRealLit)
      {
        return Val == ((VCExprRealLit) that).Val;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprFloatLit : VCExprLiteral
  {
    public readonly BigFloat Val;

    internal VCExprFloatLit(BigFloat val)
      : base(Type.GetFloatType(val.SignificandSize, val.ExponentSize))
    {
      this.Val = val;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprFloatLit)
      {
        return Val == ((VCExprFloatLit) that).Val;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprRModeLit : VCExprLiteral
  {
    public readonly RoundingMode Val;

    internal VCExprRModeLit(RoundingMode val)
      : base(Type.RMode)
    {
      this.Val = val;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprRModeLit)
      {
        return Val == ((VCExprRModeLit) that).Val;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  public class VCExprStringLit : VCExprLiteral
  {
    public readonly String Val;

    internal VCExprStringLit(String val)
      : base(Type.RMode)
    {
      this.Val = val;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprStringLit)
      {
        return Val == ((VCExprStringLit) that).Val;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Val.GetHashCode() * 72321;
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Operator expressions with fixed arity
  [ContractClassFor(typeof(VCExprNAry))]
  public abstract class VCExprNAryContracts : VCExprNAry
  {
    public VCExprNAryContracts()
      : base(null)
    {
    }

    public override VCExpr this[int index]
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpr>() != null);
        throw new NotImplementedException();
      }
    }
  }

  [ContractClass(typeof(VCExprNAryContracts))]
  public abstract class VCExprNAry : VCExpr
  {
    public override string ToString()
    {
      return $"${Op}(${String.Join(", ", Arguments)})";
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerable<VCExpr> Arguments
    {
      get
      {
        for (int i = 0; i < Arity; ++i)
        {
          yield return this[i];
        }
      }
    }
    
    public readonly VCExprOp Op;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Op != null);
      Contract.Invariant(Cce.NonNullElements(EMPTY_TYPE_LIST));
      Contract.Invariant(Cce.NonNullElements(EMPTY_VCEXPR_LIST));
    }

    public int Arity
    {
      get { return Op.Arity; }
    }

    public int TypeParamArity
    {
      get { return Op.TypeParamArity; }
    }

    public int Length
    {
      get { return Arity; }
    }

    // the sub-expressions of the expression
    public abstract VCExpr /*!*/ this[int index] { get; }

    // the type arguments
    public abstract List<Type /*!*/> /*!*/ TypeArguments { get; }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprNAry)
      {
        // we compare the subterms iteratively (not recursively)
        // to avoid stack overflows

        VCExprNAryEnumerator enum0 = new VCExprNAryEnumerator(this);
        VCExprNAryEnumerator enum1 = new VCExprNAryEnumerator((VCExprNAry) that);

        while (true)
        {
          bool next0 = enum0.MoveNext();
          bool next1 = enum1.MoveNext();
          if (next0 != next1)
          {
            return false;
          }

          if (!next0)
          {
            return true;
          }

          VCExprNAry nextExprNAry0 = enum0.Current as VCExprNAry;
          VCExprNAry nextExprNAry1 = enum1.Current as VCExprNAry;

          if ((nextExprNAry0 == null) != (nextExprNAry1 == null))
          {
            return false;
          }

          if (nextExprNAry0 != null && nextExprNAry1 != null)
          {
            if (!nextExprNAry0.Op.Equals(nextExprNAry1.Op))
            {
              return false;
            }
          }
          else
          {
            if (!Cce.NonNull(enum0.Current).Equals(enum1.Current))
            {
              return false;
            }
          }
        }
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return HelperFuns.PolyHash(Op.GetHashCode() * 123 + Arity * 61521, 3, this.Arguments);
    }

    internal VCExprNAry(VCExprOp op)
    {
      Contract.Requires(op != null);
      this.Op = op;
    }

    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }

    public Result Accept<Result, Arg>(IVCExprOpVisitor<Result, Arg> visitor, Arg arg)
    {
      Contract.Requires(visitor != null);
      return Op.Accept(this, visitor, arg);
    }

    internal static readonly List<Type /*!*/> /*!*/
      EMPTY_TYPE_LIST = new List<Type /*!*/>();

    internal static readonly List<VCExpr /*!*/> /*!*/
      EMPTY_VCEXPR_LIST = new List<VCExpr /*!*/>();

    public IEnumerable<VCExpr> UniformArguments
    {
      get
      {
        var enumerator = new VCExprNAryUniformOpEnumerator(this);
        while (enumerator.MoveNext())
        {
          VCExprNAry naryExpr = enumerator.Current as VCExprNAry;
          if (naryExpr == null || !naryExpr.Op.Equals(this.Op))
          {
            yield return (VCExpr) enumerator.Current;
          }
        }
      }
    }
  }

  // We give specialised implementations for nullary, unary and binary expressions

  internal class VCExprNullary : VCExprNAry
  {
    private readonly Type ExprType;

    [ContractInvariantMethod]
    void loneinvariant()
    {
      Contract.Invariant(ExprType != null);
    }

    public override Type Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }

    public override VCExpr this[int index]
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        Contract.Assert(false);
        throw new Cce.UnreachableException(); // no arguments
      }
    }

    // the type arguments
    public override List<Type /*!*/> /*!*/ TypeArguments
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Type>>()));
        return EMPTY_TYPE_LIST;
      }
    }

    internal VCExprNullary(VCExprOp op)
      : base(op)
    {
      Contract.Requires(op != null);
      Contract.Requires(op.Arity == 0 && op.TypeParamArity == 0);
      this.ExprType = op.InferType(EMPTY_VCEXPR_LIST, EMPTY_TYPE_LIST);
    }
  }

  internal class VCExprUnary : VCExprNAry
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Argument != null);
      Contract.Invariant(ExprType != null);
    }

    private readonly VCExpr /*!*/
      Argument;

    private readonly Type /*!*/
      ExprType;

    public override Type /*!*/ Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }

    public override VCExpr /*!*/ this[int index]
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        Contract.Assume(index == 0);
        return Argument;
      }
    }

    // the type arguments
    public override List<Type /*!*/> /*!*/ TypeArguments
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Type>>()));
        return EMPTY_TYPE_LIST;
      }
    }

    internal VCExprUnary(VCExprOp op, List<VCExpr> arguments)
      : base(op)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Requires(op.Arity == 1 && op.TypeParamArity == 0 && arguments.Count == 1);

      this.Argument = arguments[0];
      this.ExprType =
        op.InferType(arguments, EMPTY_TYPE_LIST);
    }

    internal VCExprUnary(VCExprOp op, VCExpr argument)
      : base(op)
    {
      Contract.Requires(argument != null);
      Contract.Requires(op != null);
      Contract.Requires(op.Arity == 1 && op.TypeParamArity == 0);

      this.Argument = argument;
      // PR: could be optimised so that the argument does
      // not have to be boxed in an array each time
      this.ExprType =
        op.InferType(HelperFuns.ToNonNullList(argument), EMPTY_TYPE_LIST);
    }
  }

  internal class VCExprBinary : VCExprNAry
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Argument0 != null);
      Contract.Invariant(Argument1 != null);
      Contract.Invariant(ExprType != null);
    }

    private readonly VCExpr Argument0;
    private readonly VCExpr Argument1;
    private readonly Type ExprType;

    public override Type Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }

    public override VCExpr this[int index]
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        switch (index)
        {
          case 0:
            return Argument0;
          case 1:
            return Argument1;
          default:
          {
            Contract.Assert(false);
            throw new Cce.UnreachableException();
          }
        }
      }
    }

    // the type arguments
    public override List<Type /*!*/> /*!*/ TypeArguments
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Type>>()));
        return EMPTY_TYPE_LIST;
      }
    }

    internal VCExprBinary(VCExprOp op, List<VCExpr> arguments)
      : base(op)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Requires(op.Arity == 2 && op.TypeParamArity == 0 && arguments.Count == 2);

      this.Argument0 = arguments[0];
      this.Argument1 = arguments[1];
      this.ExprType = op.InferType(arguments, EMPTY_TYPE_LIST);
    }

    internal VCExprBinary(VCExprOp op, VCExpr argument0, VCExpr argument1)
      : base(op)
    {
      Contract.Requires(argument1 != null);
      Contract.Requires(argument0 != null);
      Contract.Requires(op != null);
      Contract.Requires(op.Arity == 2 && op.TypeParamArity == 0);
      this.Argument0 = argument0;
      this.Argument1 = argument1;
      // PR: could be optimised so that the arguments do
      // not have to be boxed in an array each time
      this.ExprType =
        op.InferType(HelperFuns.ToNonNullList(argument0, argument1),
          EMPTY_TYPE_LIST);
    }
  }

  internal class VCExprMultiAry : VCExprNAry
  {
    private readonly List<VCExpr /*!*/> /*!*/ arguments;

    private readonly List<Type /*!*/> /*!*/
      TypeArgumentsAttr;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(arguments));
      Contract.Invariant(Cce.NonNullElements(TypeArgumentsAttr));
      Contract.Invariant(ExprType != null);
    }


    private readonly Type /*!*/
      ExprType;

    public override Type /*!*/ Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        return ExprType;
      }
    }

    public override VCExpr /*!*/ this[int index]
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpr>() != null);

        Contract.Assume(index >= 0 && index < Arity);
        return Cce.NonNull(arguments)[index];
      }
    }

    // the type arguments
    public override List<Type /*!*/> /*!*/ TypeArguments
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Type>>()));
        return TypeArgumentsAttr;
      }
    }

    internal VCExprMultiAry(VCExprOp op, List<VCExpr> arguments)
      : base(op)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      this.arguments = arguments;
      this.TypeArgumentsAttr = EMPTY_TYPE_LIST;
      this.ExprType = op.InferType(arguments, TypeArgumentsAttr);
    }

    internal VCExprMultiAry(VCExprOp op, List<VCExpr> arguments, List<Type /*!*/> /*!*/ typeArguments)
      : base(op)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(typeArguments));
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Requires(arguments.Count > 2 || typeArguments.Count > 0);
      Contract.Requires(op.Arity == arguments.Count);
      Contract.Requires(op.TypeParamArity == typeArguments.Count);
      this.arguments = arguments;
      this.TypeArgumentsAttr = typeArguments;
      this.ExprType = op.InferType(arguments, typeArguments);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // The various operators available
  [ContractClass(typeof(VCExprOpContracts))]
  public abstract class VCExprOp
  {
    // the number of value parameters
    public abstract int Arity { get; }

    // the number of type parameters
    public abstract int TypeParamArity { get; }

    public abstract Type /*!*/ InferType(List<VCExpr /*!*/> /*!*/ args, List<Type /*!*/> /*!*/ typeArgs);

    public virtual Result Accept<Result, Arg>(VCExprNAry expr, IVCExprOpVisitor<Result, Arg> visitor, Arg arg)
    {
      Contract.Requires(visitor != null);
      Contract.Requires(expr != null);
      if (VCExpressionGenerator.SingletonOpDict.TryGetValue(this, out var op))
      {
        switch (op)
        {
          case VCExpressionGenerator.SingletonOp.NotOp:
            return visitor.VisitNotOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.EqOp:
            return visitor.VisitEqOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.NeqOp:
            return visitor.VisitNeqOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.AndOp:
            return visitor.VisitAndOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.OrOp:
            return visitor.VisitOrOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ImpliesOp:
            return visitor.VisitImpliesOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.AddOp:
            return visitor.VisitAddOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.SubOp:
            return visitor.VisitSubOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.MulOp:
            return visitor.VisitMulOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.DivOp:
            return visitor.VisitDivOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ModOp:
            return visitor.VisitModOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.RealDivOp:
            return visitor.VisitRealDivOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.PowOp:
            return visitor.VisitPowOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.LtOp:
            return visitor.VisitLtOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.LeOp:
            return visitor.VisitLeOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.GtOp:
            return visitor.VisitGtOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.GeOp:
            return visitor.VisitGeOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.SubtypeOp:
            return visitor.VisitSubtypeOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.Subtype3Op:
            return visitor.VisitSubtype3Op(expr, arg);
          case VCExpressionGenerator.SingletonOp.BvConcatOp:
            return visitor.VisitBvConcatOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ToIntOp:
            return visitor.VisitToIntOp(expr, arg);
          case VCExpressionGenerator.SingletonOp.ToRealOp:
            return visitor.VisitToRealOp(expr, arg);
          default:
            Contract.Assert(false);
            throw new Cce.UnreachableException();
        }
      }
      else
      {
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      }
    }
  }

  [ContractClassFor(typeof(VCExprOp))]
  abstract class VCExprOpContracts : VCExprOp
  {
    public override Type InferType(List<VCExpr> args, List<Type> typeArgs)
    {
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Requires(Cce.NonNullElements(typeArgs));
      Contract.Ensures(Contract.Result<Type>() != null);

      throw new NotImplementedException();
    }
  }

  public class VCExprNAryOp : VCExprOp
  {
    private readonly Type OpType;
    private readonly int OpArity;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(OpType != null);
    }

    public override int Arity
    {
      get { return OpArity; }
    }

    public override int TypeParamArity
    {
      get { return 0; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return OpType;
    }

    internal VCExprNAryOp(int arity, Type type)
    {
      Contract.Requires(type != null);
      this.OpArity = arity;
      this.OpType = type;
    }
  }

  public class VCExprDistinctOp : VCExprNAryOp
  {
    internal VCExprDistinctOp(int arity)
      : base(arity, Type.Bool)
    {
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprDistinctOp)
      {
        return Arity == ((VCExprDistinctOp) that).Arity;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Arity * 917632481;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitDistinctOp(expr, arg);
    }
  }

  public class VCExprFieldAccessOp : VCExprOp
  {
    public DatatypeTypeCtorDecl DatatypeTypeCtorDecl;

    private DatatypeAccessor DatatypeAccessor;
    
    public int ConstructorIndex => DatatypeAccessor.ConstructorIndex;
    
    public int FieldIndex => DatatypeAccessor.FieldIndex;
    
    public override int Arity => 1;
    
    public override int TypeParamArity => 0; // datatypes work only with monomorphization
    
    public override Type InferType(List<VCExpr> args, List<Type> typeArgs)
    {
      Contract.Assert(typeArgs.Count == 0);
      return DatatypeTypeCtorDecl.Constructors[ConstructorIndex].InParams[FieldIndex].TypedIdent.Type;
    }
    
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }
      if (that is VCExprFieldAccessOp thatOp)
      {
        return DatatypeTypeCtorDecl.Equals(thatOp.DatatypeTypeCtorDecl) &&
               ConstructorIndex == thatOp.ConstructorIndex && FieldIndex == thatOp.FieldIndex;
      }
      return false;
    }
    
    public override int GetHashCode()
    {
      return Arity * 1212481;
    }

    internal VCExprFieldAccessOp(DatatypeTypeCtorDecl datatypeTypeCtorDecl, DatatypeAccessor datatypeAccessor)
    {
      DatatypeTypeCtorDecl = datatypeTypeCtorDecl;
      DatatypeAccessor = datatypeAccessor;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      return visitor.VisitFieldAccessOp(expr, arg);
    }
  }
  
  public class VCExprIsConstructorOp : VCExprOp
  {
    public DatatypeTypeCtorDecl DatatypeTypeCtorDecl;
    
    public int ConstructorIndex;
    
    public override int Arity => 1;
    
    public override int TypeParamArity => 0; // datatypes work only with monomorphization
    
    public override Type InferType(List<VCExpr> args, List<Type> typeArgs)
    {
      Contract.Assert(typeArgs.Count == 0);
      return Type.Bool;
    }
    
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }
      if (that is VCExprIsConstructorOp thatOp)
      {
        return DatatypeTypeCtorDecl.Equals(thatOp.DatatypeTypeCtorDecl) &&
               ConstructorIndex == thatOp.ConstructorIndex;
      }
      return false;
    }
    
    public override int GetHashCode()
    {
      return Arity * 1212481;
    }

    internal VCExprIsConstructorOp(DatatypeTypeCtorDecl datatypeTypeCtorDecl, int constructorIndex)
    {
      DatatypeTypeCtorDecl = datatypeTypeCtorDecl;
      ConstructorIndex = constructorIndex;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      return visitor.VisitIsConstructorOp(expr, arg);
    }
  }
  
  public class VCExprSelectOp : VCExprOp
  {
    private readonly int MapArity;
    private readonly int MapTypeParamArity;

    public override int Arity
    {
      get { return MapArity + 1; }
    }

    public override int TypeParamArity
    {
      get { return MapTypeParamArity; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      MapType /*!*/
        mapType = args[0].Type.AsMap;
      Contract.Assert(TypeParamArity == mapType.TypeParameters.Count);
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      for (int i = 0; i < TypeParamArity; ++i)
      {
        subst.Add(mapType.TypeParameters[i], typeArgs[i]);
      }

      return mapType.Result.Substitute(subst);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprSelectOp)
      {
        return Arity == ((VCExprSelectOp) that).Arity &&
               TypeParamArity == ((VCExprSelectOp) that).TypeParamArity;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Arity * 1212481 + TypeParamArity * 298741;
    }

    internal VCExprSelectOp(int arity, int typeParamArity)
    {
      Contract.Requires(0 <= arity && 0 <= typeParamArity);
      this.MapArity = arity;
      this.MapTypeParamArity = typeParamArity;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitSelectOp(expr, arg);
    }
  }

  public class VCExprStoreOp : VCExprOp
  {
    private readonly int MapArity;
    private readonly int MapTypeParamArity;

    public override int Arity
    {
      get { return MapArity + 2; }
    }

    // stores never need explicit type parameters, because also the
    // rhs is a value argument
    public override int TypeParamArity
    {
      get { return MapTypeParamArity; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return args[0].Type;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprStoreOp)
      {
        return Arity == ((VCExprStoreOp) that).Arity;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Arity * 91361821;
    }

    internal VCExprStoreOp(int arity, int typeParamArity)
    {
      Contract.Requires(0 <= arity && 0 <= typeParamArity);
      this.MapArity = arity;
      this.MapTypeParamArity = typeParamArity;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitStoreOp(expr, arg);
    }
  }

  public class VCExprIfThenElseOp : VCExprOp
  {
    public override int Arity
    {
      get { return 3; }
    }

    public override int TypeParamArity
    {
      get { return 0; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return args[1].Type;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprIfThenElseOp)
      {
        return true;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return 1;
    }

    internal VCExprIfThenElseOp()
    {
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitIfThenElseOp(expr, arg);
    }
  }

  public class VCExprSoftOp : VCExprCustomOp
  {
    public readonly int Weight;

    public VCExprSoftOp(int weight) : base("soft##dummy", 2, Microsoft.Boogie.Type.Bool)
    {
      Weight = weight;
    }
  }

  public class VCExprCustomOp : VCExprOp
  {
    public readonly string /*!*/
      Name;

    int arity;

    public readonly Type /*!*/
      Type;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Name != null);
      Contract.Invariant(Type != null);
    }

    public VCExprCustomOp(string /*!*/ name, int arity, Type /*!*/ type)
    {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.Name = name;
      this.arity = arity;
      this.Type = type;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      VCExprCustomOp t = that as VCExprCustomOp;
      if (t == null)
      {
        return false;
      }

      return this.Name == t.Name && this.arity == t.arity && this.Type == t.Type;
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override int GetHashCode()
    {
      int h = Name.GetHashCode();
      h = 7823 * h + arity;
      h = 7823 * h + Type.GetHashCode();
      return h;
    }

    public override int Arity
    {
      get { return arity; }
    }

    public override int TypeParamArity
    {
      get { return 0; }
    }

    public override Type /*!*/ InferType(List<VCExpr /*!*/> /*!*/ args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires((cce.NonNullElements(args)));
      //Contract.Requires((cce.NonNullElements(typeArgs)));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry /*!*/ expr,
      IVCExprOpVisitor<Result, Arg> /*!*/ visitor,
      Arg arg)
    {
      //Contract.Requires(expr != null);
      //Contract.Requires(visitor != null);
      return visitor.VisitCustomOp(expr, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Float operators

  public class VCExprBinaryFloatOp : VCExprOp
  {
    public readonly int Significand;
    public readonly int Exponent;
    private string op;

    public override int Arity
    {
      get { return 2; }
    }

    public override int TypeParamArity
    {
      get { return 2; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      switch (op)
      {
        case ("+"):
        case ("-"):
        case ("*"):
        case ("/"):
          return Type.GetFloatType(Significand, Exponent);
        case ("<="):
        case ("<"):
        case (">="):
        case (">"):
        case ("=="):
        case ("!="):
          return Type.Bool;
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException();
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprBinaryFloatOp)
      {
        return this.Exponent == ((VCExprBinaryFloatOp) that).Exponent &&
               this.Significand == ((VCExprBinaryFloatOp) that).Significand;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Exponent * 81748912 + Significand * 67867979;
    }

    internal VCExprBinaryFloatOp(int sig, int exp, string op)
    {
      this.Exponent = exp;
      this.Significand = sig;
      this.op = op;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      switch (op)
      {
        case ("+"):
          return visitor.VisitFloatAddOp(expr, arg);
        case ("-"):
          return visitor.VisitFloatSubOp(expr, arg);
        case ("*"):
          return visitor.VisitFloatMulOp(expr, arg);
        case ("/"):
          return visitor.VisitFloatDivOp(expr, arg);
        case ("<="):
          return visitor.VisitFloatLeqOp(expr, arg);
        case ("<"):
          return visitor.VisitFloatLtOp(expr, arg);
        case (">="):
          return visitor.VisitFloatGeqOp(expr, arg);
        case (">"):
          return visitor.VisitFloatGtOp(expr, arg);
        case ("=="):
          return visitor.VisitEqOp(expr, arg);
        case ("!="):
          return visitor.VisitNeqOp(expr, arg);
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException();
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Bitvector operators

  public class VCExprBvOp : VCExprOp
  {
    public readonly int Bits;

    public override int Arity
    {
      get { return 1; }
    }

    public override int TypeParamArity
    {
      get { return 0; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type.GetBvType(Bits);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprBvOp)
      {
        return this.Bits == ((VCExprBvOp) that).Bits;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Bits * 81748912;
    }

    internal VCExprBvOp(int bits)
    {
      this.Bits = bits;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBvOp(expr, arg);
    }
  }

  public class VCExprBvExtractOp : VCExprOp
  {
    public readonly int Start;
    public readonly int End;
    public readonly int Total; // the number of bits from which the End-Start bits are extracted

    public override int Arity
    {
      get { return 1; }
    }

    public override int TypeParamArity
    {
      get { return 0; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type.GetBvType(End - Start);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprBvExtractOp)
      {
        VCExprBvExtractOp /*!*/
          thatExtract = (VCExprBvExtractOp) that;
        return this.Start == thatExtract.Start && this.End == thatExtract.End && this.Total == thatExtract.Total;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Start * 81912 + End * 978132 + Total * 571289;
    }

    internal VCExprBvExtractOp(int start, int end, int total)
    {
      Contract.Requires(0 <= start && start <= end && end <= total);
      this.Start = start;
      this.End = end;
      this.Total = total;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBvExtractOp(expr, arg);
    }
  }

  public class VCExprBvConcatOp : VCExprOp
  {
    public readonly int LeftSize;
    public readonly int RightSize;

    public override int Arity
    {
      get { return 2; }
    }

    public override int TypeParamArity
    {
      get { return 0; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      return Type.GetBvType(args[0].Type.BvBits + args[1].Type.BvBits);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprBvConcatOp)
      {
        VCExprBvConcatOp thatConcat = (VCExprBvConcatOp) that;
        return this.LeftSize == thatConcat.LeftSize && this.RightSize == thatConcat.RightSize;
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return LeftSize * 81912 + RightSize * 978132;
    }

    internal VCExprBvConcatOp(int leftSize, int rightSize)
    {
      Contract.Requires(0 <= leftSize && 0 <= rightSize);
      this.LeftSize = leftSize;
      this.RightSize = rightSize;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBvConcatOp(expr, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // References to user-defined Boogie functions

  public class VCExprBoogieFunctionOp : VCExprOp
  {
    public readonly Function Func;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Func != null);
    }


    public override int Arity
    {
      get { return Func.InParams.Count; }
    }

    public override int TypeParamArity
    {
      get { return Func.TypeParameters.Count; }
    }

    public override Type InferType(List<VCExpr> args, List<Type /*!*/> /*!*/ typeArgs)
    {
      //Contract.Requires(cce.NonNullElements(typeArgs));
      //Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(TypeParamArity == Func.TypeParameters.Count);
      if (TypeParamArity == 0)
      {
        return Cce.NonNull(Func.OutParams[0]).TypedIdent.Type;
      }

      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst = new Dictionary<TypeVariable /*!*/, Type /*!*/>(TypeParamArity);
      for (int i = 0; i < TypeParamArity; ++i)
      {
        subst.Add(Func.TypeParameters[i], typeArgs[i]);
      }

      return Cce.NonNull(Func.OutParams[0]).TypedIdent.Type.Substitute(subst);
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprBoogieFunctionOp)
      {
        return this.Func.Equals(((VCExprBoogieFunctionOp) that).Func);
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Func.GetHashCode() + 18731;
    }

    // we require that the result type of the expression is specified, because we
    // do not want to perform full type inference at this point
    internal VCExprBoogieFunctionOp(Function func)
    {
      Contract.Requires(func != null);
      this.Func = func;
    }

    public override Result Accept<Result, Arg>(
      VCExprNAry expr,
      IVCExprOpVisitor<Result, Arg> visitor,
      Arg arg)
    {
      //Contract.Requires(visitor != null);
      //Contract.Requires(expr != null);
      return visitor.VisitBoogieFunctionOp(expr, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Binders (quantifiers and let-expressions). We introduce our own class for
  // term variables, but use the Boogie-AST class for type variables

  public enum VCExprVarKind
  {
    Normal, // A normal variable
    Soft,   // A variable used for tracking an assumption labeled with the `:soft` attribute
    Try,    // A variable used for tracking an assumption labeled with the `:try` attribute
    Assert, // A variable used for tracking an assertion labeled with the `:id` attribute
    Assume  // A variable used for tracking an assumption labeled with the `:id` attribute
  }

  public class VCExprVar : VCExpr
  {
    // the name of the variable. Note that the name is not used for comparison,
    // i.e., there can be two distinct variables with the same name
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Name != null);
      Contract.Invariant(VarType != null);
    }

    public readonly string /*!*/
      Name;

    private readonly Type /*!*/
      VarType;

    public VCExprVarKind VarKind { get; }

    public override Type /*!*/ Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);
        return VarType;
      }
    }

    internal VCExprVar(string name, Type type, VCExprVarKind kind = VCExprVarKind.Normal)
    {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
      this.Name = KindPrefix(kind) + name;
      this.VarType = type;
      this.VarKind = kind;
    }

    private string KindPrefix(VCExprVarKind kind)
    {
      return kind switch
      {
        VCExprVarKind.Assert => "assert$$",
        VCExprVarKind.Assume => "assume$$",
        VCExprVarKind.Soft => "soft$$",
        VCExprVarKind.Try => "try$$",
        VCExprVarKind.Normal => "",
        _ => throw new Cce.UnreachableException()
      };
    }

    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
    
    // For VCExprVar, equality is based on reference comparison.
    // Two different heap-allocated variables with the same name 
    // are considered semantically-different variables.
    // Name clashes are handled in NameClashResolver.cs.
  }

  public class VCExprConstant : VCExprVar
  {
    internal VCExprConstant(string name, Type type) : base(name, type)
    {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
    }
  }

  public abstract class VCExprBinder : VCExpr
  {
    public readonly VCExpr /*!*/
      Body;

    public readonly List<TypeVariable /*!*/> /*!*/
      TypeParameters;

    public readonly List<VCExprVar /*!*/> /*!*/
      BoundVars;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Body != null);
      Contract.Invariant(Cce.NonNullElements(TypeParameters));
      Contract.Invariant(Cce.NonNullElements(BoundVars));
    }


    public override Type /*!*/ Type
    {
      get
      {
        Contract.Ensures(Contract.Result<Type>() != null);

        return Body.Type;
      }
    }

    internal VCExprBinder(List<TypeVariable /*!*/> /*!*/ typeParams, List<VCExprVar /*!*/> /*!*/ boundVars, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(Cce.NonNullElements(boundVars));
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Requires(boundVars.Count + typeParams.Count > 0); // only nontrivial binders ...
      this.TypeParameters = typeParams;
      this.BoundVars = boundVars;
      this.Body = body;
    }
  }

  public class VCTrigger
  {
    public readonly bool Pos;

    public readonly List<VCExpr /*!*/> /*!*/
      Exprs;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Exprs != null);
    }


    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCTrigger)
      {
        VCTrigger /*!*/
          thatTrigger = (VCTrigger) that;
        return this.Pos == thatTrigger.Pos &&
               HelperFuns.SameElements(this.Exprs, thatTrigger.Exprs);
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return (Pos ? 913821 : 871334) +
             HelperFuns.PolyHash(123, 7, this.Exprs);
    }

    public VCTrigger(bool pos, List<VCExpr> exprs)
    {
      Contract.Requires(Cce.NonNullElements(exprs));
      this.Pos = pos;
      this.Exprs = exprs;
    }
  }

  public class VCQuantifierInfo
  {
    public readonly string qid;
    public readonly int uniqueId;
    public readonly int weight;

    // The entries in instantiationLabels correspond to the
    // bound variables of the quantifier to which this info is attached.
    // The bound variable v may be instantiated by terms in the pool associated
    // with any label in instantiationLabels[v].
    public readonly Dictionary<VCExprVar, HashSet<string>> instantiationLabels;

    // When the quantifier to which this info is attached is skolemized,
    // each expression in instantiationExprs[L] is added to the pool of
    // expressions for label L.
    public readonly Dictionary<string, HashSet<VCExpr>> instantiationExprs;
    
    public VCQuantifierInfo(string qid, int uniqueId)
    {
      this.qid = qid;
      this.uniqueId = uniqueId;
      this.weight = 1;
      this.instantiationLabels = new Dictionary<VCExprVar, HashSet<string>>();
      this.instantiationExprs = new Dictionary<string, HashSet<VCExpr>>();
    }

    public VCQuantifierInfo(string qid, int uniqueId, int weight)
    {
      this.qid = qid;
      this.uniqueId = uniqueId;
      this.weight = weight;
      this.instantiationLabels = new Dictionary<VCExprVar, HashSet<string>>();
      this.instantiationExprs = new Dictionary<string, HashSet<VCExpr>>();
    }

    public VCQuantifierInfo(string qid, int uniqueId, int weight,
      Dictionary<VCExprVar, HashSet<string>> instantiationLabels, Dictionary<string, HashSet<VCExpr>> instantiationExprs)
    {
      this.qid = qid;
      this.uniqueId = uniqueId;
      this.weight = weight;
      this.instantiationLabels = instantiationLabels;
      this.instantiationExprs = instantiationExprs;
    }
  }

  public enum Quantifier
  {
    ALL,
    EX
  }

  public class VCExprQuantifier : VCExprBinder
  {
    public readonly Quantifier Quan;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Info != null);
      Contract.Invariant(Cce.NonNullElements(Triggers));
    }

    public readonly List<VCTrigger /*!*/> /*!*/
      Triggers;

    public readonly VCQuantifierInfo Info;
    
    // Equality is /not/ modulo bound renaming at this point
    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprQuantifier)
      {
        VCExprQuantifier /*!*/
          thatQuan = (VCExprQuantifier) that;
        return this.Quan == thatQuan.Quan &&
               HelperFuns.SameElements(this.Triggers, thatQuan.Triggers) &&
               HelperFuns.SameElements(this.TypeParameters, thatQuan.TypeParameters) &&
               HelperFuns.SameElements(this.BoundVars, thatQuan.BoundVars) &&
               this.Body.Equals(thatQuan.Body);
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return Quan.GetHashCode() +
             HelperFuns.PolyHash(973219, 7, TypeParameters) +
             HelperFuns.PolyHash(998431, 9, BoundVars) +
             HelperFuns.PolyHash(123, 11, Triggers);
    }

    internal VCExprQuantifier(Quantifier kind, List<TypeVariable /*!*/> /*!*/ typeParams,
      List<VCExprVar /*!*/> /*!*/ boundVars, List<VCTrigger /*!*/> /*!*/ triggers, VCQuantifierInfo info, VCExpr body)
      : base(typeParams, boundVars, body)
    {
      Contract.Requires(body != null);
      Contract.Requires(info != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(boundVars));
      Contract.Requires(Cce.NonNullElements(typeParams));

      this.Quan = kind;
      this.Triggers = triggers;
      this.Info = info;
    }

    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }

  /////////////////////////////////////////////////////////////////////////////////
  // Let-Bindings

  public class VCExprLetBinding
  {
    public readonly VCExprVar V;
    public readonly VCExpr E;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(V != null);
      Contract.Invariant(E != null);
    }


    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprLetBinding)
      {
        VCExprLetBinding /*!*/
          thatB = (VCExprLetBinding) that;
        return this.V.Equals(thatB.V) && this.E.Equals(thatB.E);
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return V.GetHashCode() * 71261 + E.GetHashCode();
    }

    internal VCExprLetBinding(VCExprVar v, VCExpr e)
    {
      Contract.Requires(e != null);
      Contract.Requires(v != null);
      this.V = v;
      this.E = e;
      Contract.Assert(v.Type.Equals(e.Type));
    }
  }

  public class VCExprLet : VCExprBinder, IEnumerable<VCExprLetBinding /*!*/>
  {
    private readonly List<VCExprLetBinding /*!*/> /*!*/
      Bindings;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(Bindings));
    }


    public int Length
    {
      get { return Bindings.Count; }
    }

    public VCExprLetBinding this[int index]
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExprLetBinding>() != null);
        return Bindings[index];
      }
    }

    [Pure]
    [Reads(ReadsAttribute.Reads.Nothing)]
    public override bool Equals(object that)
    {
      if (Object.ReferenceEquals(this, that))
      {
        return true;
      }

      if (that is VCExprLet)
      {
        VCExprLet /*!*/
          thatLet = (VCExprLet) that;
        return this.Body.Equals(thatLet.Body) &&
               HelperFuns.SameElements(this, (VCExprLet) that);
      }

      return false;
    }

    [Pure]
    public override int GetHashCode()
    {
      return HelperFuns.PolyHash(Body.GetHashCode(), 9, Bindings);
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    public IEnumerator<VCExprLetBinding /*!*/> /*!*/ GetEnumerator()
    {
      Contract.Ensures(Cce.NonNullElements(Contract.Result<IEnumerator<VCExprLetBinding>>()));
      return Bindings.GetEnumerator();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator System.Collections.IEnumerable.GetEnumerator()
    {
      Contract.Ensures(Contract.Result<IEnumerator>() != null);
      return Bindings.GetEnumerator();
    }

    private static List<VCExprVar /*!*/> /*!*/ toSeq(List<VCExprLetBinding /*!*/> /*!*/ bindings)
    {
      Contract.Requires(Cce.NonNullElements(bindings));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      List<VCExprVar> res = new List<VCExprVar>();
      foreach (VCExprLetBinding /*!*/ b in bindings)
      {
        res.Add(b.V);
      }

      return res;
    }

    internal VCExprLet(List<VCExprLetBinding /*!*/> /*!*/ bindings, VCExpr /*!*/ body)
      : base(new List<TypeVariable /*!*/>(), toSeq(bindings), body)
    {
      Contract.Requires(Cce.NonNullElements(bindings));
      Contract.Requires(body != null);
      this.Bindings = bindings;
    }

    public override Result Accept<Result, Arg>(IVCExprVisitor<Result, Arg> visitor, Arg arg)
    {
      //Contract.Requires(visitor != null);
      return visitor.Visit(this, arg);
    }
  }
}