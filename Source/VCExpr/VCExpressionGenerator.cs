using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie
{
  public class VCExpressionGenerator
  {
    public static readonly VCExpr False = new VCExprLiteral(Type.Bool);
    public static readonly VCExpr True = new VCExprLiteral(Type.Bool);
    public const string ControlFlowName = "ControlFlow";

    private Function ControlFlowFunction = null;

    public VCExpr ControlFlowFunctionApplication(VCExpr e1, VCExpr e2)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(e2 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (ControlFlowFunction == null)
      {
        Formal /*!*/
          first = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Int), true);
        Formal /*!*/
          second = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Int), true);
        List<Variable> inputs = new List<Variable>();
        inputs.Add(first);
        inputs.Add(second);
        Formal /*!*/
          returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Int), false);
        ControlFlowFunction = new Function(Token.NoToken, ControlFlowName, inputs, returnVar);
      }

      List<VCExpr /*!*/> args = new List<VCExpr /*!*/>();
      args.Add(e1);
      args.Add(e2);
      return Function(BoogieFunctionOp(ControlFlowFunction), args);
    }

    public VCExpr /*!*/ Integer(BigNum x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprIntLit(x);
    }

    public VCExpr /*!*/ Real(BigDec x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprRealLit(x);
    }

    public VCExpr /*!*/ Float(BigFloat x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprFloatLit(x);
    }

    public VCExpr /*!*/ RMode(RoundingMode x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprRModeLit(x);
    }

    public VCExpr /*!*/ String(String x)
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return new VCExprStringLit(x);
    }

    public VCExpr /*!*/ Function(VCExprOp /*!*/ op,
      List<VCExpr /*!*/> /*!*/ arguments,
      List<Type /*!*/> /*!*/ typeArguments)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Requires(Cce.NonNullElements(typeArguments));
      if (typeArguments.Count > 0)
      {
        return new VCExprMultiAry(op, arguments, typeArguments);
      }

      switch (arguments.Count)
      {
        case 0:
          return new VCExprNullary(op);
        case 1:
          return new VCExprUnary(op, arguments);
        case 2:
          return new VCExprBinary(op, arguments);
        default:
          return new VCExprMultiAry(op, arguments);
      }
    }

    public VCExpr /*!*/ Function(VCExprOp /*!*/ op, List<VCExpr /*!*/> /*!*/ arguments)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(op, arguments, VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr /*!*/ Function(VCExprOp /*!*/ op, params VCExpr[] /*!*/ arguments)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));

      return Function(op,
        HelperFuns.ToNonNullList(arguments),
        VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr /*!*/ Function(VCExprOp /*!*/ op, VCExpr[] /*!*/ arguments, Type[] /*!*/ typeArguments)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Requires(Cce.NonNullElements(typeArguments));
      Contract.Ensures(Contract.Result<VCExpr>() != null);


      return Function(op,
        HelperFuns.ToNonNullList(arguments),
        HelperFuns.ToNonNullList(typeArguments));
    }

    public VCExpr /*!*/ Function(Function /*!*/ op, List<VCExpr /*!*/> /*!*/ arguments)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(BoogieFunctionOp(op), arguments, VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr /*!*/ Function(Function /*!*/ op, params VCExpr[] /*!*/ arguments)
    {
      Contract.Requires(Cce.NonNullElements(arguments));
      Contract.Requires(op != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(BoogieFunctionOp(op), arguments);
    }


    // The following method should really be called "ReduceLeft". It must
    // only be used for the binary operators "and" and "or"
    public VCExpr /*!*/ NAry(VCExprOp /*!*/ op, List<VCExpr /*!*/> /*!*/ args)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return NAry(op, args.ToArray());
    }

    public VCExpr /*!*/ NAry(VCExprOp /*!*/ op, params VCExpr[] /*!*/ args)
    {
      Contract.Requires(op != null);
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Requires(op == AndOp || op == OrOp);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      bool and = (op == AndOp);

      VCExpr /*!*/
        e = and ? True : False;
      foreach (VCExpr a in args)
      {
        e = and ? AndSimp(e, Cce.NonNull(a)) : OrSimp(e, Cce.NonNull(a));
      }

      return e;
    }

    ////////////////////////////////////////////////////////////////////////////////

    public static readonly VCExprOp NotOp = new VCExprNAryOp(1, Type.Bool);
    public static readonly VCExprOp EqOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp NeqOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp AndOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp OrOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp ImpliesOp = new VCExprNAryOp(2, Type.Bool);

    public VCExprDistinctOp DistinctOp(int arity)
    {
      Contract.Ensures(Contract.Result<VCExprDistinctOp>() != null);

      return new VCExprDistinctOp(arity);
    }

    public VCExpr /*!*/ Not(List<VCExpr /*!*/> /*!*/ args)
    {
      Contract.Requires(args != null);
      Contract.Requires(args.Count == 1);
      Contract.Requires(args[0] != null);
      return Function(NotOp, args);
    }

    public VCExpr /*!*/ Not(VCExpr /*!*/ e0)
    {
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(NotOp, e0);
    }

    public VCExpr /*!*/ Eq(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      return Function(EqOp, e0, e1);
    }

    public VCExpr /*!*/ Neq(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(NeqOp, e0, e1);
    }

    public VCExpr /*!*/ And(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(AndOp, e0, e1);
    }

    public VCExpr /*!*/ Gt(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return Function(GtOp, e0, e1);
    }

    public VCExpr /*!*/ Add(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      VCExprOp op = Cce.NonNull(Cce.NonNull(e0).Type).IsInt ? AddIOp : AddROp;
      return Function(op, e0, e1);
    }

    public VCExpr /*!*/ Or(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(OrOp, e0, e1);
    }

    public VCExpr /*!*/ Implies(VCExpr /*!*/ e0, VCExpr /*!*/ e1)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(ImpliesOp, e0, e1);
    }

    public VCExpr /*!*/ Distinct(List<VCExpr /*!*/> /*!*/ args)
    {
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (args.Count <= 1)
      {
        // trivial case
        return True;
      }

      return Function(DistinctOp(args.Count), args);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Versions of the propositional operators that automatically simplify in
    // certain cases (for example, if one of the operators is True or False)

    public VCExpr NotSimp(VCExpr e0)
    {
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(True))
      {
        return False;
      }

      if (e0.Equals(False))
      {
        return True;
      }

      return Not(e0);
    }

    public VCExpr AndSimp(VCExpr e0, VCExpr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(True))
      {
        return e1;
      }

      if (e1.Equals(True))
      {
        return e0;
      }

      if (e0.Equals(False) || e1.Equals(False))
      {
        return False;
      }

      return And(e0, e1);
    }

    public VCExpr OrSimp(VCExpr e0, VCExpr e1)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(False))
      {
        return e1;
      }

      if (e1.Equals(False))
      {
        return e0;
      }

      if (e0.Equals(True) || e1.Equals(True))
      {
        return True;
      }

      return Or(e0, e1);
    }

    public VCExpr ImpliesSimp(VCExpr e0, VCExpr e1, bool aggressive = true)
    {
      Contract.Requires(e1 != null);
      Contract.Requires(e0 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (e0.Equals(True))
      {
        return e1;
      }

      if (e1.Equals(False))
      {
        return NotSimp(e0);
      }

      if (e0.Equals(False) || e1.Equals(True))
      {
        return True;
      }
      // attempt to save on the depth of expressions (to reduce chances of stack overflows)
      while (aggressive && e1 is VCExprBinary)
      {
        VCExprBinary n = (VCExprBinary) e1;
        if (n.Op == ImpliesOp)
        {
          if (AndSize(n[0]) <= AndSize(e0))
          {
            // combine the antecedents
            e0 = And(e0, n[0]);
            e1 = n[1];
            continue;
          }
        }

        break;
      }

      return Implies(e0, e1);
    }

    ///<summary>
    /// Returns some measure of the number of conjuncts in e.  This could be the total number of conjuncts in all
    /// top-most layers of the expression, or it can simply be the length of the left-prong of this and-tree.  The
    /// important thing is that: AndSize(e0) >= AndSize(31) ==> AndSize(And(e0,e1)) > AndSize(e0).
    ///</summary>
    int AndSize(VCExpr e)
    {
      Contract.Requires(e != null);
      int n = 1;
      while (true)
      {
        VCExprNAry nary = e as VCExprNAry;
        if (nary != null && nary.Op == AndOp && 2 <= nary.Arity)
        {
          e = nary[0];
          n++;
        }
        else
        {
          return n;
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Further operators

    public static readonly VCExprOp AddIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp AddROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp SubIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp SubROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp MulIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp MulROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp DivIOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp DivROp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp ModOp = new VCExprNAryOp(2, Type.Int);
    public static readonly VCExprOp PowOp = new VCExprNAryOp(2, Type.Real);
    public static readonly VCExprOp LtOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp LeOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp GtOp = new VCExprNAryOp(2, Type.Bool);
    public static readonly VCExprOp GeOp = new VCExprNAryOp(2, Type.Bool);
    
    public static readonly VCExprOp IfThenElseOp = new VCExprIfThenElseOp();
    public static readonly VCExprOp ToIntOp = new VCExprNAryOp(1, Type.Int);
    public static readonly VCExprOp ToRealOp = new VCExprNAryOp(1, Type.Real);

    public static readonly VCExprOp TickleBoolOp = new VCExprCustomOp("tickleBool", 1, Type.Bool);

    public static readonly VCExprOp TimeoutDiagnosticsOp = new VCExprCustomOp("timeoutDiagnostics", 1, Type.Bool);

    // These operators are temporarily added to VCExprs to track where labels for optimization and unsat
    // core generation should go, but don't appear in the final SMT-Lib output.
    public static readonly VCExprOp MinimizeOp = new VCExprCustomOp("minimize##dummy", 2, Type.Bool);
    public static readonly VCExprOp MaximizeOp = new VCExprCustomOp("maximize##dummy", 2, Type.Bool);
    public static readonly VCExprOp NamedAssumeOp = new VCExprCustomOp("named_assume##dummy", 2, Type.Bool);
    public static readonly VCExprOp NamedAssertOp = new VCExprCustomOp("named_assert##dummy", 2, Type.Bool);

    public VCExprOp BoogieFunctionOp(Function func)
    {
      Contract.Requires(func != null);
      Contract.Ensures(Contract.Result<VCExprOp>() != null);
      return new VCExprBoogieFunctionOp(func);
    }

    // Float nodes

    public VCExprOp BinaryFloatOp(int sig, int exp, string op)
    {
      Contract.Requires(exp > 0);
      Contract.Requires(sig > 0);
      Contract.Requires(op != null);
      Contract.Ensures(Contract.Result<VCExprOp>() != null);
      return new VCExprBinaryFloatOp(sig, exp, op);
    }

    // Bitvector nodes

    public VCExpr Bitvector(BvConst bv)
    {
      Contract.Requires(bv != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprBvOp(bv.Bits), Integer(bv.Value));
    }

    public VCExpr BvExtract(VCExpr bv, int bits, int start, int end)
    {
      Contract.Requires(bv != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprBvExtractOp(start, end, bits), bv);
    }

    public VCExpr BvConcat(VCExpr bv1, VCExpr bv2)
    {
      Contract.Requires(bv2 != null);
      Contract.Requires(bv1 != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Function(new VCExprBvConcatOp(bv1.Type.BvBits, bv2.Type.BvBits), bv1, bv2);
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Dispatcher for the visitor

    // the declared singleton operators
    internal enum SingletonOp
    {
      NotOp,
      EqOp,
      NeqOp,
      AndOp,
      OrOp,
      ImpliesOp,
      AddOp,
      SubOp,
      MulOp,
      DivOp,
      ModOp,
      RealDivOp,
      PowOp,
      LtOp,
      LeOp,
      GtOp,
      GeOp,
      SubtypeOp,
      Subtype3Op,
      BvConcatOp,
      ToIntOp,
      ToRealOp,
      ToFloatOp
    }

    internal static Dictionary<VCExprOp /*!*/, SingletonOp> /*!*/
      SingletonOpDict;

    [ContractInvariantMethod]
    void MiscInvariant()
    {
      Contract.Invariant(SingletonOpDict != null);
    }


    static VCExpressionGenerator()
    {
      ScopedNamer.AddBoogieDeterminedName(ControlFlowName);

      SingletonOpDict = new Dictionary<VCExprOp /*!*/, SingletonOp>();
      SingletonOpDict.Add(NotOp, SingletonOp.NotOp);
      SingletonOpDict.Add(EqOp, SingletonOp.EqOp);
      SingletonOpDict.Add(NeqOp, SingletonOp.NeqOp);
      SingletonOpDict.Add(AndOp, SingletonOp.AndOp);
      SingletonOpDict.Add(OrOp, SingletonOp.OrOp);
      SingletonOpDict.Add(ImpliesOp, SingletonOp.ImpliesOp);
      SingletonOpDict.Add(AddIOp, SingletonOp.AddOp);
      SingletonOpDict.Add(AddROp, SingletonOp.AddOp);
      SingletonOpDict.Add(SubIOp, SingletonOp.SubOp);
      SingletonOpDict.Add(SubROp, SingletonOp.SubOp);
      SingletonOpDict.Add(MulIOp, SingletonOp.MulOp);
      SingletonOpDict.Add(MulROp, SingletonOp.MulOp);
      SingletonOpDict.Add(DivIOp, SingletonOp.DivOp);
      SingletonOpDict.Add(DivROp, SingletonOp.RealDivOp);
      SingletonOpDict.Add(ModOp, SingletonOp.ModOp);
      SingletonOpDict.Add(PowOp, SingletonOp.PowOp);
      SingletonOpDict.Add(LtOp, SingletonOp.LtOp);
      SingletonOpDict.Add(LeOp, SingletonOp.LeOp);
      SingletonOpDict.Add(GtOp, SingletonOp.GtOp);
      SingletonOpDict.Add(GeOp, SingletonOp.GeOp);
      SingletonOpDict.Add(ToIntOp, SingletonOp.ToIntOp);
      SingletonOpDict.Add(ToRealOp, SingletonOp.ToRealOp);
    }

    ////////////////////////////////////////////////////////////////////////////////


    // Let-bindings

    public VCExprLetBinding LetBinding(VCExprVar v, VCExpr e)
    {
      Contract.Requires(e != null);
      Contract.Requires(v != null);
      Contract.Ensures(Contract.Result<VCExprLetBinding>() != null);
      return new VCExprLetBinding(v, e);
    }

    // A "real" let expression. All let-bindings happen simultaneously, i.e.,
    // at this level the order of the bindings does not matter. It is possible to
    // create expressions like   "let x = y, y = 5 in ...". All bound variables are
    // bound in all bound terms/formulas and can occur there, but the dependencies
    // have to be acyclic
    public VCExpr Let(List<VCExprLetBinding> bindings, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(Cce.NonNullElements(bindings));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (bindings.Count == 0)
      {
        // no empty let-bindings
        return body;
      }

      return new VCExprLet(bindings, body);
    }

    public VCExpr Let(VCExpr body, params VCExprLetBinding[] bindings)
    {
      Contract.Requires(body != null);
      Contract.Requires((Cce.NonNullElements(bindings)));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Let(HelperFuns.ToNonNullList(bindings), body);
    }


    /// <summary>
    /// In contrast to the previous method, the following methods are not a general LET.
    ///  Instead, it
    /// is a boolean "LET b = P in Q", where P and Q are predicates, that is allowed to be
    /// encoded as "(b == P) ==> Q" or even as "(P ==> b) ==> Q"
    /// (or "(P ==> b) and Q" in negative positions).
    /// The method assumes that the variables in the bindings are unique in the entire formula
    /// to be produced, which allows the implementation to ignore scope issues in the event that
    /// it needs to generate an alternate expression for LET.
    /// </summary>

    // Turn let-bindings let v = E in ... into implications E ==> v
    public VCExpr AsImplications(List<VCExprLetBinding> bindings)
    {
      Contract.Requires(Cce.NonNullElements(bindings));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr /*!*/
        antecedents = True;
      foreach (VCExprLetBinding b in bindings)
      {
        // turn "LET_binding v = E" into "v <== E"
        antecedents = AndSimp(antecedents, Implies(b.E, b.V));
      }

      return antecedents;
    }

    // Turn let-bindings let v = E in ... into equations v == E
    public VCExpr AsEquations(List<VCExprLetBinding> bindings)
    {
      Contract.Requires(Cce.NonNullElements(bindings));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr /*!*/
        antecedents = True;
      foreach (VCExprLetBinding b in bindings)
      {
        // turn "LET_binding v = E" into "v <== E"
        antecedents = AndSimp(antecedents, Eq(b.E, b.V));
      }

      return antecedents;
    }


    // Maps

    public VCExpr Select(params VCExpr[] allArgs)
    {
      return Select(allArgs.ToList(), VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr Select(VCExpr[] allArgs, Type[] typeArgs)
    {
      return Select(allArgs.ToList(), typeArgs.ToList());
    }

    public VCExpr Select(List<VCExpr> allArgs, List<Type> typeArgs)
    {
      return Function(new VCExprSelectOp(allArgs.Count - 1, typeArgs.Count), allArgs, typeArgs);
    }

    public VCExpr Store(params VCExpr[] allArgs)
    {
      return Store(allArgs.ToList(), VCExprNAry.EMPTY_TYPE_LIST);
    }

    public VCExpr Store(VCExpr[] allArgs, Type[] typeArgs)
    {
      return Store(allArgs.ToList(), typeArgs.ToList());
    }

    public VCExpr Store(List<VCExpr> allArgs, List<Type> typeArgs)
    {
      return Function(new VCExprStoreOp(allArgs.Count - 2, typeArgs.Count), allArgs, typeArgs);
    }

    // Quantifiers

    public VCExpr Quantify(Quantifier quan, List<TypeVariable /*!*/> /*!*/ typeParams, List<VCExprVar /*!*/> /*!*/ vars,
      List<VCTrigger /*!*/> /*!*/ triggers, VCQuantifierInfo info, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(info != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return new VCExprQuantifier(quan, typeParams, vars, triggers, info, body);
    }

    public VCExpr Forall(List<TypeVariable /*!*/> /*!*/ typeParams, List<VCExprVar /*!*/> /*!*/ vars,
      List<VCTrigger /*!*/> /*!*/ triggers, VCQuantifierInfo info, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(info != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.ALL, typeParams, vars, triggers, info, body);
    }

    public VCExpr Forall(List<VCExprVar /*!*/> /*!*/ vars, List<VCTrigger /*!*/> /*!*/ triggers, string qid, int weight,
      VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(qid != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.ALL, new List<TypeVariable /*!*/>(), vars,
        triggers, new VCQuantifierInfo(qid, -1, weight), body);
    }

    public VCExpr Forall(List<VCExprVar /*!*/> /*!*/ vars, List<VCTrigger /*!*/> /*!*/ triggers, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.ALL, new List<TypeVariable /*!*/>(), vars,
        triggers, new VCQuantifierInfo(null, -1), body);
    }

    public VCExpr Forall(VCExprVar var, VCTrigger trigger, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(trigger != null);
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Forall(HelperFuns.ToNonNullList(var), HelperFuns.ToNonNullList(trigger), body);
    }

    public VCExpr Exists(List<TypeVariable /*!*/> /*!*/ typeParams, List<VCExprVar /*!*/> /*!*/ vars,
      List<VCTrigger /*!*/> /*!*/ triggers, VCQuantifierInfo info, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(info != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.EX, typeParams, vars, triggers, info, body);
    }

    public VCExpr Exists(List<VCExprVar /*!*/> /*!*/ vars, List<VCTrigger /*!*/> /*!*/ triggers, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(Cce.NonNullElements(triggers));
      Contract.Requires(Cce.NonNullElements(vars));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Quantify(Quantifier.EX, new List<TypeVariable /*!*/>(), vars,
        triggers, new VCQuantifierInfo(null, -1), body);
    }

    public VCExpr Exists(VCExprVar var, VCTrigger trigger, VCExpr body)
    {
      Contract.Requires(body != null);
      Contract.Requires(trigger != null);
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Exists(HelperFuns.ToNonNullList(var), HelperFuns.ToNonNullList(trigger), body);
    }

    public VCTrigger Trigger(bool pos, List<VCExpr> exprs)
    {
      Contract.Requires(Cce.NonNullElements(exprs));
      Contract.Ensures(Contract.Result<VCTrigger>() != null);
      return new VCTrigger(pos, exprs);
    }

    public VCTrigger Trigger(bool pos, params VCExpr[] exprs)
    {
      Contract.Requires(exprs != null);
      Contract.Requires((Contract.ForAll(0, exprs.Length, i => exprs[i] != null)));
      Contract.Ensures(Contract.Result<VCTrigger>() != null);
      return Trigger(pos, HelperFuns.ToNonNullList(exprs));
    }

    // Reference to a bound or free variable

    public VCExprVar Variable(string name, Type type, VCExprVarKind kind = VCExprVarKind.Normal)
    {
      Contract.Requires(type != null);
      Contract.Requires(name != null);
      Contract.Ensures(Contract.Result<VCExprVar>() != null);
      return new VCExprVar(name, type, kind);
    }
  }
}
