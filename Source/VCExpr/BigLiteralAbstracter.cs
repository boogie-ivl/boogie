using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;

// Code for replacing large integer literals in VCExpr with
// constants. This is necessary for Simplify, which cannot deal with
// literals larger than 32 bits.

namespace Microsoft.Boogie.VCExprAST
{
  public class BigLiteralAbstracter : MutatingVCExprVisitor<bool>, ICloneable
  {
    public BigLiteralAbstracter(VCExpressionGenerator gen)
      : base(gen)
    {
      Contract.Requires(gen != null);
      DummyVar = gen.Variable("x", Type.Int);
      IncAxioms = new List<VCExpr>();
      Literals = new List<KeyValuePair<BigNum, VCExprVar>>();
    }

    private BigLiteralAbstracter(BigLiteralAbstracter abstracter)
      : base(abstracter.Gen)
    {
      Contract.Requires(abstracter != null);
      DummyVar = abstracter.DummyVar;
      IncAxioms = new List<VCExpr>(abstracter.IncAxioms);
      Literals = new List<KeyValuePair<BigNum, VCExprVar>>(abstracter.Literals);
    }

    public Object Clone()
    {
      Contract.Ensures(Contract.Result<Object>() != null);

      return new BigLiteralAbstracter(this);
    }

    private static readonly BigNum ConstantDistance = BigNum.FromLong(100000);

    private static readonly BigNum NegConstantDistance = BigNum.FromLong(-100000);

    // distance twice plus one
    private static readonly BigNum ConstantDistanceTPO = BigNum.FromLong(200001);
    private static readonly BigNum ConstantDistancePO = BigNum.FromLong(100001);

    public VCExpr Abstract(VCExpr expr)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Mutate(expr, true);
    }

    ////////////////////////////////////////////////////////////////////////////

    // list in which axioms are incrementally collected
    private readonly List<VCExpr /*!*/> /*!*/
      IncAxioms;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(IncAxioms));
    }

    private void AddAxiom(VCExpr /*!*/ axiom)
    {
      Contract.Requires(axiom != null);
      IncAxioms.Add(axiom);
    }

    // Return all axioms that were added since the last time NewAxioms
    // was called
    public VCExpr GetNewAxioms()
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr res = Gen.NAry(VCExpressionGenerator.AndOp, IncAxioms);
      IncAxioms.Clear();
      return res;
    }

    ////////////////////////////////////////////////////////////////////////////

    // All named integer literals known to the visitor, in ascending
    // order. Such literals are always positive, and the distance
    // between two literals is always more than ConstantDistance.
    private readonly List<KeyValuePair<BigNum, VCExprVar /*!*/>> /*!*/
      Literals;

    [ContractInvariantMethod]
    void ObjectInvariat()
    {
      Contract.Invariant(Literals != null);
      Contract.Invariant(Contract.ForAll(Literals, i => i.Value != null));
    }


    private class EntryComparerC : IComparer<KeyValuePair<BigNum, VCExprVar /*!*/>>
    {
      public int Compare(KeyValuePair<BigNum, VCExprVar /*!*/> a,
        KeyValuePair<BigNum, VCExprVar /*!*/> b)
      {
        //Contract.Requires(a.Value!=null);
        //Contract.Requires(b.Value!=null);
        return a.Key.CompareTo(b.Key);
      }
    }

    private static readonly EntryComparerC EntryComparer = new EntryComparerC();

    // variable used when searching for entries in the literal list
    private readonly VCExprVar /*!*/
      DummyVar;

    [ContractInvariantMethod]
    void ObjectInvarint()
    {
      Contract.Invariant(DummyVar != null);
    }


    ////////////////////////////////////////////////////////////////////////////

    // Construct an expression to represent the given (large) integer
    // literal. Constants are defined and axiomatised if necessary
    private VCExpr Represent(BigNum lit)
    {
      Contract.Requires((NegConstantDistance > lit || lit > ConstantDistance));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (lit.IsNegative)
      {
        return Gen.Function(VCExpressionGenerator.SubIOp,
          Gen.Integer(BigNum.ZERO), RepresentPos(lit.Neg));
      }
      else
      {
        return RepresentPos(lit);
      }
    }

    private VCExpr RepresentPos(BigNum lit)
    {
      Contract.Requires((lit > ConstantDistance));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      int index = GetIndexFor(lit);
      if (index >= 0)
      {
        // precise match
        return Literals[index].Value;
      }

      // check whether a constant is defined that is at most
      // ConstantDistance away from lit
      index = ~index;
      VCExpr res = null;
      BigNum resDistance = ConstantDistancePO;

      if (index > 0)
      {
        BigNum dist = lit - Literals[index - 1].Key;
        if (dist < resDistance)
        {
          resDistance = dist;
          res = Gen.Function(VCExpressionGenerator.AddIOp,
            Literals[index - 1].Value, Gen.Integer(dist));
        }
      }

      if (index < Literals.Count)
      {
        BigNum dist = Literals[index].Key - lit;
        if (dist < resDistance)
        {
          resDistance = dist;
          res = Gen.Function(VCExpressionGenerator.SubIOp,
            Literals[index].Value, Gen.Integer(dist));
        }
      }

      if (res != null)
      {
        return res;
      }

      // otherwise, define a new constant to represent this literal
      return AddConstantFor(lit);
    }

    private VCExpr AddConstantFor(BigNum lit)
    {
      Contract.Requires((lit > ConstantDistance));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExprVar res = Gen.Variable("int#" + lit, Type.Int);
      int index = GetIndexFor(lit);
      Contract.Assert(index < 0);
      index = ~index;

      Literals.Insert(index, new KeyValuePair<BigNum, VCExprVar>(lit, res));

      // relate the new constant to the predecessor and successor
      if (index > 0)
      {
        DefineRelationship(Literals[index - 1].Value, Literals[index - 1].Key,
          res, lit);
      }
      else
      {
        DefineRelationship(Gen.Integer(BigNum.ZERO), BigNum.ZERO, res, lit);
      }

      if (index < Literals.Count - 1)
      {
        DefineRelationship(res, lit,
          Literals[index + 1].Value, Literals[index + 1].Key);
      }

      return res;
    }

    private void DefineRelationship(VCExpr /*!*/ aExpr, BigNum aValue,
      VCExpr /*!*/ bExpr, BigNum bValue)
    {
      Contract.Requires(aValue < bValue);
      Contract.Requires(aExpr != null);
      Contract.Requires(bExpr != null);

      BigNum dist = bValue - aValue;
      VCExpr distExpr = Gen.Function(VCExpressionGenerator.SubIOp, bExpr, aExpr);
      if (dist <= ConstantDistanceTPO)
      {
        // constants that are sufficiently close to each other are put
        // into a precise relationship
        AddAxiom(Gen.Eq(distExpr, Gen.Integer(dist)));
      }
      else
      {
        AddAxiom(Gen.Function(VCExpressionGenerator.GtOp,
          distExpr, Gen.Integer(ConstantDistanceTPO)));
      }
    }

    private int GetIndexFor(BigNum lit)
    {
      return Literals.BinarySearch(
        new KeyValuePair<BigNum, VCExprVar>(lit, DummyVar),
        EntryComparer);
    }

    ////////////////////////////////////////////////////////////////////////////

    public override VCExpr Visit(VCExprLiteral node, bool arg)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExprIntLit intLit = node as VCExprIntLit;
      if (intLit != null)
      {
        if (NegConstantDistance > intLit.Val || intLit.Val > ConstantDistance)
        {
          return Represent(intLit.Val);
        }
      }

      return node;
    }
  }
}