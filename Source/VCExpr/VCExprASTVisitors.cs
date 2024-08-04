using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

// Some visitor skeletons for the VCExpression AST

namespace Microsoft.Boogie.VCExprAST
{
  [ContractClass(typeof(IVCExprVisitorContracts<,>))]
  public interface IVCExprVisitor<Result, Arg>
  {
    Result Visit(VCExprLiteral /*!*/ node, Arg arg);
    Result Visit(VCExprNAry /*!*/ node, Arg arg);
    Result Visit(VCExprVar /*!*/ node, Arg arg);
    Result Visit(VCExprQuantifier /*!*/ node, Arg arg);
    Result Visit(VCExprLet /*!*/ node, Arg arg);
  }

  [ContractClassFor(typeof(IVCExprVisitor<,>))]
  public abstract class IVCExprVisitorContracts<Result, Arg> : IVCExprVisitor<Result, Arg>
  {
    #region IVCExprVisitor Members

    public Result Visit(VCExprLiteral node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprVar node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprQuantifier node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result Visit(VCExprLet node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    #endregion
  }

  [ContractClass(typeof(IVCExprOpVisitorContracts<,>))]
  public interface IVCExprOpVisitor<Result, Arg>
  {
    Result VisitNotOp(VCExprNAry node, Arg arg);
    Result VisitEqOp(VCExprNAry node, Arg arg);
    Result VisitNeqOp(VCExprNAry node, Arg arg);
    Result VisitAndOp(VCExprNAry node, Arg arg);
    Result VisitOrOp(VCExprNAry node, Arg arg);
    Result VisitImpliesOp(VCExprNAry node, Arg arg);
    Result VisitDistinctOp(VCExprNAry node, Arg arg);
    Result VisitFieldAccessOp(VCExprNAry node, Arg arg);
    Result VisitIsConstructorOp(VCExprNAry node, Arg arg);
    Result VisitSelectOp(VCExprNAry node, Arg arg);
    Result VisitStoreOp(VCExprNAry node, Arg arg);
    Result VisitFloatAddOp(VCExprNAry node, Arg arg);
    Result VisitFloatSubOp(VCExprNAry node, Arg arg);
    Result VisitFloatMulOp(VCExprNAry node, Arg arg);
    Result VisitFloatDivOp(VCExprNAry node, Arg arg);
    Result VisitFloatLeqOp(VCExprNAry node, Arg arg);
    Result VisitFloatLtOp(VCExprNAry node, Arg arg);
    Result VisitFloatGeqOp(VCExprNAry node, Arg arg);
    Result VisitFloatGtOp(VCExprNAry node, Arg arg);
    Result VisitFloatEqOp(VCExprNAry node, Arg arg);
    Result VisitFloatNeqOp(VCExprNAry node, Arg arg);
    Result VisitBvOp(VCExprNAry node, Arg arg);
    Result VisitBvExtractOp(VCExprNAry node, Arg arg);
    Result VisitBvConcatOp(VCExprNAry node, Arg arg);
    Result VisitAddOp(VCExprNAry node, Arg arg);
    Result VisitSubOp(VCExprNAry node, Arg arg);
    Result VisitMulOp(VCExprNAry node, Arg arg);
    Result VisitDivOp(VCExprNAry node, Arg arg);
    Result VisitModOp(VCExprNAry node, Arg arg);
    Result VisitRealDivOp(VCExprNAry node, Arg arg);
    Result VisitPowOp(VCExprNAry node, Arg arg);
    Result VisitLtOp(VCExprNAry node, Arg arg);
    Result VisitLeOp(VCExprNAry node, Arg arg);
    Result VisitGtOp(VCExprNAry node, Arg arg);
    Result VisitGeOp(VCExprNAry node, Arg arg);
    Result VisitSubtypeOp(VCExprNAry node, Arg arg);
    Result VisitSubtype3Op(VCExprNAry node, Arg arg);
    Result VisitToIntOp(VCExprNAry node, Arg arg);
    Result VisitToRealOp(VCExprNAry node, Arg arg);
    Result VisitBoogieFunctionOp(VCExprNAry node, Arg arg);
    Result VisitIfThenElseOp(VCExprNAry node, Arg arg);
    Result VisitCustomOp(VCExprNAry node, Arg arg);
  }

  [ContractClassFor(typeof(IVCExprOpVisitor<,>))]
  public abstract class IVCExprOpVisitorContracts<Result, Arg> : IVCExprOpVisitor<Result, Arg>
  {
    #region IVCExprOpVisitor<Result,Arg> Members

    public Result VisitNotOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitEqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitNeqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitAndOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitOrOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitImpliesOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitDistinctOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFieldAccessOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }
    
    public Result VisitIsConstructorOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }
    
    public Result VisitSelectOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitStoreOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatAddOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatSubOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatMulOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatDivOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatLeqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatLtOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatGeqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatGtOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatEqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitFloatNeqOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBvOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBvExtractOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBvConcatOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitAddOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSubOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitMulOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitDivOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitModOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitRealDivOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitPowOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitLtOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitLeOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitGtOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitGeOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSubtypeOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitSubtype3Op(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitToIntOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitToRealOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitToFloat(VCExprNAry node, Arg arg) //TODO: modify later
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitBoogieFunctionOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitIfThenElseOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    public Result VisitCustomOp(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }

    #endregion
  }

  //////////////////////////////////////////////////////////////////////////////
  // Standard implementations that make it easier to create own visitors

  // Simple traversal of VCExprs. The Visit implementations work
  // recursively, apart from the implementation for VCExprNAry that
  // uses a stack when applied to nested nodes with the same
  // operator, e.g., (AND (AND (AND ...) ...) ...). This is necessary
  // to avoid stack overflows


  [ContractClass(typeof(TraversingVCExprVisitorContracts<,>))]
  public abstract class TraversingVCExprVisitor<Result, Arg>
    : IVCExprVisitor<Result, Arg>
  {
    protected abstract Result StandardResult(VCExpr /*!*/ node, Arg arg);

    public Result Traverse(VCExpr node, Arg arg)
    {
      Contract.Requires(node != null);
      return node.Accept(this, arg);
    }

    public virtual Result Visit(VCExprLiteral node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result Visit(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      Result res = StandardResult(node, arg);
      
      if (node.TypeParamArity == 0 &&
          (node.Op == VCExpressionGenerator.AndOp ||
           node.Op == VCExpressionGenerator.OrOp ||
           node.Op == VCExpressionGenerator.ImpliesOp))
      {
        Contract.Assert(node.Op != null);
        VCExprOp op = node.Op;
        HashSet<VCExprOp> ops = new HashSet<VCExprOp>();
        ops.Add(VCExpressionGenerator.AndOp);
        ops.Add(VCExpressionGenerator.OrOp);
        ops.Add(VCExpressionGenerator.ImpliesOp);
        IEnumerator enumerator = new VCExprNAryMultiUniformOpEnumerator(node, ops);
        while (enumerator.MoveNext())
        {
          VCExpr expr = Cce.NonNull((VCExpr) enumerator.Current);
          VCExprNAry naryExpr = expr as VCExprNAry;
          if (naryExpr == null || !ops.Contains(naryExpr.Op))
          {
            expr.Accept(this, arg);
          }
          else
          {
            StandardResult(expr, arg);
          }
        }
      }
      else
      {
        foreach (VCExpr e in node.Arguments)
        {
          Contract.Assert(e != null);
          e.Accept(this, arg);
        }
      }

      return res;
    }

    public virtual Result Visit(VCExprVar node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result Visit(VCExprQuantifier node, Arg arg)
    {
      //Contract.Requires(node != null);
      Result res = StandardResult(node, arg);
      foreach (VCTrigger /*!*/ trigger in node.Triggers)
      {
        Contract.Assert(trigger != null);
        foreach (VCExpr /*!*/ expr in trigger.Exprs)
        {
          Contract.Assert(expr != null);
          expr.Accept(this, arg);
        }
      }

      node.Body.Accept(this, arg);
      return res;
    }

    public virtual Result Visit(VCExprLet node, Arg arg)
    {
      //Contract.Requires(node != null);
      Result res = StandardResult(node, arg);
      // visit the bound expressions first
      foreach (VCExprLetBinding /*!*/ binding in node)
      {
        Contract.Assert(binding != null);
        binding.E.Accept(this, arg);
      }

      node.Body.Accept(this, arg);
      return res;
    }
  }

  [ContractClassFor(typeof(TraversingVCExprVisitor<,>))]
  public abstract class TraversingVCExprVisitorContracts<Result, Arg> : TraversingVCExprVisitor<Result, Arg>
  {
    protected override Result StandardResult(VCExpr node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }
  }
  //////////////////////////////////////////////////////////////////////////////
  // Class to iterate over the nodes of a tree of VCExprNAry. This is
  // used to avoid handling such VCExpr recursively, which can easily
  // lead to stack overflows

  public class VCExprNAryEnumerator : IEnumerator
  {
    private readonly VCExprNAry /*!*/
      CompleteExpr;

    private VCExpr CurrentExpr = null;

    private readonly Stack<VCExpr /*!*/> /*!*/
      ExprTodo = new Stack<VCExpr /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(CompleteExpr != null);
      Contract.Invariant(Cce.NonNullElements(ExprTodo));
    }

    public VCExprNAryEnumerator(VCExprNAry completeExpr)
    {
      Contract.Requires(completeExpr != null);
      this.CompleteExpr = completeExpr;
      Stack<VCExpr /*!*/> /*!*/
        exprTodo = new Stack<VCExpr /*!*/>();
      exprTodo.Push(completeExpr);
      ExprTodo = exprTodo;
    }

    // Method using which a subclass can decide whether the
    // subexpressions of an expression should be enumerated as well
    // The default is to enumerate all nodes
    protected virtual bool Descend(VCExprNAry expr)
    {
      Contract.Requires(expr != null);
      return true;
    }

    ////////////////////////////////////////////////////////////////////////////

    public bool MoveNext()
    {
      if (ExprTodo.Count == 0)
      {
        return false;
      }

      CurrentExpr = ExprTodo.Pop();
      VCExprNAry currentNAry = CurrentExpr as VCExprNAry;
      if (currentNAry != null && Descend(currentNAry))
      {
        for (int i = currentNAry.Arity - 1; i >= 0; --i)
        {
          ExprTodo.Push(currentNAry[i]);
        }
      }

      return true;
    }

    public object Current
    {
      get { return Cce.NonNull(CurrentExpr); }
    }

    public void Reset()
    {
      ExprTodo.Clear();
      CurrentExpr = null;
      ExprTodo.Push(CompleteExpr);
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  public class VCExprNAryUniformOpEnumerator : VCExprNAryEnumerator
  {
    private readonly VCExprOp /*!*/
      Op;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Op != null);
    }

    public VCExprNAryUniformOpEnumerator(VCExprNAry completeExpr)
      : base(completeExpr)
    {
      Contract.Requires(completeExpr != null);

      this.Op = completeExpr.Op;
    }

    protected override bool Descend(VCExprNAry expr)
    {
      //Contract.Requires(expr != null);
      return expr.Op.Equals(Op) &&
             // we never skip nodes with type parameters
             // (those are too interesting ...)
             expr.TypeParamArity == 0;
    }
  }

  public class VCExprNAryMultiUniformOpEnumerator : VCExprNAryEnumerator
  {
    private readonly HashSet<VCExprOp> Ops;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Ops != null);
    }

    public VCExprNAryMultiUniformOpEnumerator(VCExprNAry completeExpr, HashSet<VCExprOp> ops)
      : base(completeExpr)
    {
      Contract.Requires(completeExpr != null);

      this.Ops = ops;
    }

    protected override bool Descend(VCExprNAry expr)
    {
      return Ops.Contains(expr.Op) && expr.TypeParamArity == 0;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Visitor that knows about the variables bound at each location in a VCExpr

  public abstract class BoundVarTraversingVCExprVisitor<Result, Arg>
    : TraversingVCExprVisitor<Result, Arg>
  {
    private readonly IDictionary<VCExprVar, VCExpr> BoundTermVarsMap = new Dictionary<VCExprVar, VCExpr>();

    private readonly ISet<TypeVariable> BoundTypeVarsSet = new HashSet<TypeVariable>();

    protected IDictionary<VCExprVar, VCExpr> BoundTermVars => BoundTermVarsMap;

    protected ICollection<TypeVariable> BoundTypeVars => BoundTypeVarsSet;

    public override Result Visit(VCExprQuantifier node, Arg arg)
    {
      // we temporarily add bound (term and type) variables to the
      // corresponding lists
      foreach (VCExprVar v in node.BoundVars)
      {
        BoundTermVarsMap.Add(v, null);
      }

      foreach (TypeVariable v in node.TypeParameters)
      {
        BoundTypeVarsSet.Add(v);
      }

      Result res;
      try
      {
        res = VisitAfterBinding(node, arg);
      }
      finally
      {
        foreach (VCExprVar v in node.BoundVars)
        {
          BoundTermVarsMap.Remove(v);
        }

        foreach (TypeVariable v in node.TypeParameters)
        {
          BoundTypeVarsSet.Remove(v);
        }
      }

      return res;
    }

    public override Result Visit(VCExprLet node, Arg arg)
    {
      // we temporarily add bound term variables to the
      // corresponding lists
      foreach (var binding in node)
      {
        BoundTermVarsMap.Add(binding.V, binding.E);
      }

      Result res;
      try
      {
        res = VisitAfterBinding(node, arg);
      }
      finally
      {
        foreach (VCExprVar v in node.BoundVars)
        {
          BoundTermVarsMap.Remove(v);
        }
      }

      return res;
    }

    ////////////////////////////////////////////////////////////////////////////
    // The possibility is provided to look at a (quantifier or let) node
    // after its bound variables have been registered
    // (when overriding the normal visit-methods, the node will be visited
    // before the binding happens)

    protected virtual Result VisitAfterBinding(VCExprQuantifier node, Arg arg)
    {
      Contract.Requires(node != null);
      return base.Visit(node, arg);
    }

    protected virtual Result VisitAfterBinding(VCExprLet node, Arg arg)
    {
      Contract.Requires(node != null);
      return base.Visit(node, arg);
    }
  }

  public class SizeComputingVisitor : TraversingVCExprVisitor<bool, bool>
  {
    private int Size = 0;

    public static int ComputeSize(VCExpr expr)
    {
      Contract.Requires(expr != null);
      SizeComputingVisitor /*!*/
        visitor = new SizeComputingVisitor();
      visitor.Traverse(expr, true);
      return visitor.Size;
    }

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      //Contract.Requires(node != null);
      Size = Size + 1;
      return true;
    }
  }

  ////////////////////////////////////////////////////////////////////////////

  // Collect all free term and type variables in a VCExpr. Type variables
  // can occur free either in the types of bound variables, or in the type
  // parameters of VCExprNAry.

  // the result and argument (of type bool) are not used currently
  public class FreeVariableCollector : BoundVarTraversingVCExprVisitor<bool, bool>
  {
    public readonly HashSet<VCExprVar> FreeTermVars = new HashSet<VCExprVar>();

    public readonly List<TypeVariable> FreeTypeVars = new List<TypeVariable>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(FreeTermVars != null && Contract.ForAll(FreeTermVars, entry => entry != null));
      Contract.Invariant(Cce.NonNullElements(FreeTypeVars));
    }


    // not used
    protected override bool StandardResult(VCExpr node, bool arg)
    {
      //Contract.Requires(node != null);
      return true;
    }

    public static HashSet<VCExprVar> FreeTermVariables(VCExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Dictionary<VCExprVar, object>>() != null);
      Contract.Ensures(Contract.ForAll(Contract.Result<Dictionary<VCExprVar, object>>(), ftv => ftv.Key != null));
      FreeVariableCollector collector = new FreeVariableCollector();
      collector.Traverse(node, true);
      return collector.FreeTermVars;
    }

    public static List<TypeVariable> FreeTypeVariables(VCExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<TypeVariable>>()));
      FreeVariableCollector collector = new FreeVariableCollector();
      collector.Traverse(node, true);
      return collector.FreeTypeVars;
    }

    public void Reset()
    {
      FreeTermVars.Clear();
      FreeTypeVars.Clear();
    }

    public void Collect(VCExpr node)
    {
      Contract.Requires(node != null);
      Traverse(node, true);
    }

    public void Collect(Type type)
    {
      Contract.Requires(type != null);
      AddTypeVariables(type.FreeVariables.ToList());
    }

    /////////////////////////////////////////////////////////////////////////

    private void CollectTypeVariables(IEnumerable<VCExprVar /*!*/> /*!*/ boundVars)
    {
      Contract.Requires(Cce.NonNullElements(boundVars));
      foreach (VCExprVar /*!*/ var in boundVars)
      {
        Contract.Assert(var != null);
        Collect(var.Type);
      }
    }

    private void AddTypeVariables(IEnumerable<TypeVariable /*!*/> /*!*/ typeVars)
    {
      Contract.Requires(Cce.NonNullElements(typeVars));
      foreach (TypeVariable /*!*/ tvar in typeVars)
      {
        Contract.Assert(tvar != null);
        if (!BoundTypeVars.Contains(tvar) && !FreeTypeVars.Contains(tvar))
        {
          FreeTypeVars.Add(tvar);
        }
      }
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      Contract.Requires(node != null);
      if (!BoundTermVars.ContainsKey(node) && !FreeTermVars.Contains(node))
      {
        FreeTermVars.Add(node);
        Collect(node.Type);
      }

      return true;
    }

    public override bool Visit(VCExprNAry node, bool arg)
    {
      Contract.Requires(node != null);
      foreach (Type /*!*/ t in node.TypeArguments)
      {
        Contract.Assert(t != null);
        Collect(t);
      }

      return base.Visit(node, arg);
    }

    protected override bool VisitAfterBinding(VCExprQuantifier node, bool arg)
    {
      //Contract.Requires(node != null);
      CollectTypeVariables(node.BoundVars);
      return base.VisitAfterBinding(node, arg);
    }

    protected override bool VisitAfterBinding(VCExprLet node, bool arg)
    {
      //Contract.Requires(node != null);
      CollectTypeVariables(node.BoundVars);
      return base.VisitAfterBinding(node, arg);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  // Framework for mutating VCExprs

  // The Visit implementations in the following visitor work
  // recursively, apart from the implementation for VCExprNAry that
  // uses its own stack when applied to nested nodes with the same
  // operator, e.g., (AND (AND (AND ...) ...) ...). This is necessary
  // to avoid stack overflows (like in TraversingVCExprVisitor)

  ////////////////////////////////////////////////////////////////////////////
  // Substitutions and a visitor for applying substitutions. A substitution can
  // substitute both type variables and term variables

  public class VCExprSubstitution
  {
    private readonly List<IDictionary<VCExprVar /*!*/, VCExpr /*!*/> /*!*/> /*!*/
      TermSubsts;

    [ContractInvariantMethod]
    void TermSubstsInvariantMethod()
    {
      Contract.Invariant(TermSubsts != null && Contract.ForAll(TermSubsts, i => Cce.NonNullDictionaryAndValues(i)));
    }

    private readonly List<IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/> /*!*/
      TypeSubsts;

    [ContractInvariantMethod]
    void TypeSubstsInvariantMethod()
    {
      Contract.Invariant(TermSubsts != null && Contract.ForAll(TypeSubsts, i => Cce.NonNullDictionaryAndValues(i)));
    }

    public VCExprSubstitution(IDictionary<VCExprVar /*!*/, VCExpr /*!*/> /*!*/ termSubst,
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ typeSubst)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(termSubst));
      Contract.Requires(Cce.NonNullDictionaryAndValues(typeSubst));
      List<IDictionary<VCExprVar /*!*/, VCExpr /*!*/> /*!*/> /*!*/
        termSubsts =
          new List<IDictionary<VCExprVar /*!*/, VCExpr /*!*/> /*!*/>();
      termSubsts.Add(termSubst);
      List<IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/> /*!*/
        typeSubsts =
          new List<IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/>();
      typeSubsts.Add(typeSubst);
      this.TermSubsts = termSubsts;
      this.TypeSubsts = typeSubsts;
    }

    public VCExprSubstitution()
      : this(new Dictionary<VCExprVar /*!*/, VCExpr /*!*/>(), new Dictionary<TypeVariable /*!*/, Type /*!*/>())
    {
    }

    public void PushScope()
    {
      TermSubsts.Add(new Dictionary<VCExprVar /*!*/, VCExpr /*!*/>());
      TypeSubsts.Add(new Dictionary<TypeVariable /*!*/, Type /*!*/>());
    }

    public void PopScope()
    {
      TermSubsts.RemoveAt(TermSubsts.Count - 1);
      TypeSubsts.RemoveAt(TypeSubsts.Count - 1);
    }

    public VCExpr this[VCExprVar /*!*/ var]
    {
      get
      {
        Contract.Requires(var != null);
        for (int i = TermSubsts.Count - 1; i >= 0; --i)
        {
          if (TermSubsts[i].TryGetValue(var, out var res))
          {
            return res;
          }
        }

        return null;
      }
      set { TermSubsts[TermSubsts.Count - 1][var] = Cce.NonNull(value); }
    }

    public Type this[TypeVariable /*!*/ var]
    {
      get
      {
        Contract.Requires(var != null);
        for (int i = TypeSubsts.Count - 1; i >= 0; --i)
        {
          if (TypeSubsts[i].TryGetValue(var, out var res))
          {
            return res;
          }
        }

        return null;
      }
      set { TypeSubsts[TypeSubsts.Count - 1][var] = Cce.NonNull(value); }
    }

    public bool ContainsKey(VCExprVar var)
    {
      Contract.Requires(var != null);
      return this[var] != null;
    }

    public bool ContainsKey(TypeVariable var)
    {
      Contract.Requires(var != null);
      return this[var] != null;
    }

    public bool TermSubstIsEmpty
    {
      get { return TermSubsts.All(dict => !dict.Any()); }
    }

    public bool TypeSubstIsEmpty
    {
      get { return TypeSubsts.All(dict => !dict.Any()); }
    }

    public IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ ToTypeSubst
    {
      get
      {
        Contract.Ensures(Cce.NonNullDictionaryAndValues(Contract.Result<IDictionary<TypeVariable, Type>>()));
        IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
          res = new Dictionary<TypeVariable /*!*/, Type /*!*/>();
        foreach (IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ dict in TypeSubsts)
        {
          foreach (KeyValuePair<TypeVariable /*!*/, Type /*!*/> pair in dict)
          {
            Contract.Assert(Cce.NonNullElements(pair));
            // later ones overwrite earlier ones
            res[pair.Key] = pair.Value;
          }
        }

        return res;
      }
    }

    // the variables that are not mapped to themselves
    public IEnumerable<VCExprVar /*!*/> /*!*/ TermDomain
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<IEnumerable<VCExprVar>>()));
        HashSet<VCExprVar /*!*/> /*!*/
          domain = new HashSet<VCExprVar /*!*/>();
        foreach (IDictionary<VCExprVar /*!*/, VCExpr /*!*/> /*!*/ dict in TermSubsts)
        {
          Contract.Assert(dict != null);
          foreach (VCExprVar /*!*/ var in dict.Keys)
          {
            Contract.Assert(var != null);
            if (!var.Equals(this[var]))
            {
              domain.Add(var);
            }
          }
        }

        return domain;
      }
    }

    // the variables that are not mapped to themselves
    public IEnumerable<TypeVariable /*!*/> /*!*/ TypeDomain
    {
      get
      {
        Contract.Ensures(Cce.NonNullElements(Contract.Result<IEnumerable<TypeVariable>>()));
        HashSet<TypeVariable /*!*/> /*!*/
          domain = new HashSet<TypeVariable /*!*/>();
        foreach (IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ dict in TypeSubsts)
        {
          Contract.Assert(dict != null);
          foreach (TypeVariable /*!*/ var in dict.Keys)
          {
            Contract.Assert(var != null);
            if (!var.Equals(this[var]))
            {
              domain.Add(var);
            }
          }
        }

        return domain;
      }
    }

    public FreeVariableCollector /*!*/ Codomains
    {
      get
      {
        Contract.Ensures(Contract.Result<FreeVariableCollector>() != null);

        FreeVariableCollector /*!*/
          coll = new FreeVariableCollector();
        foreach (VCExprVar /*!*/ var in TermDomain)
        {
          coll.Collect(Cce.NonNull(this)[var]);
        }

        foreach (TypeVariable /*!*/ var in TypeDomain)
        {
          coll.Collect(Cce.NonNull(this)[var]);
        }

        return coll;
      }
    }

    public VCExprSubstitution Clone()
    {
      Contract.Ensures(Contract.Result<VCExprSubstitution>() != null);
      VCExprSubstitution /*!*/
        res = new VCExprSubstitution();
      foreach (IDictionary<VCExprVar /*!*/, VCExpr /*!*/> /*!*/ dict in TermSubsts)
      {
        res.TermSubsts.Add(HelperFuns.Clone(dict));
      }

      foreach (IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/ dict in TypeSubsts)
      {
        res.TypeSubsts.Add(HelperFuns.Clone(dict));
      }

      return res;
    }
  }

  /////////////////////////////////////////////////////////////////////////////////

  public class SubstitutingVCExprVisitor
    : MutatingVCExprVisitor<VCExprSubstitution /*!*/>
  {
    public SubstitutingVCExprVisitor(VCExpressionGenerator gen)
      : base(gen)
    {
      Contract.Requires(gen != null);
    }

    // when descending across a binder, we have to check that no collisions
    // or variable capture can occur. if this might happen, we replace the
    // term and type variables bound by the binder with fresh variables
    private bool CollisionPossible(IEnumerable<TypeVariable /*!*/> /*!*/ typeParams,
      IEnumerable<VCExprVar /*!*/> /*!*/ boundVars, VCExprSubstitution /*!*/ substitution)
    {
      Contract.Requires(Cce.NonNullElements(typeParams));
      Contract.Requires(Cce.NonNullElements(boundVars));
      Contract.Requires(substitution != null);
      // variables can be shadowed by a binder
      if (typeParams.Any(var => substitution.ContainsKey(var)) ||
          boundVars.Any(var => substitution.ContainsKey(var)))
      {
        return true;
      }
      // compute the codomain of the substitution
      FreeVariableCollector coll = substitution.Codomains;
      Contract.Assert(coll != null);
      // variables could be captured when applying the substitution
      return typeParams.Any(var => coll.FreeTypeVars.Contains(var)) ||
             boundVars.Any(var => coll.FreeTermVars.Contains(var));
    }

    // can be overwritten if names of bound variables are to be changed
    protected virtual string ChooseNewVariableName(string oldName)
    {
      Contract.Requires(oldName != null);
      Contract.Ensures(Contract.Result<string>() != null);
      return oldName;
    }

    // handle type parameters in VCExprNAry
    protected override VCExpr /*!*/ UpdateModifiedNode(VCExprNAry /*!*/ originalNode,
      List<VCExpr /*!*/> /*!*/ newSubExprs, bool changed, VCExprSubstitution /*!*/ substitution)
    {
      //Contract.Requires(originalNode != null);
      //Contract.Requires(cce.NonNullElements(newSubExprs));
      //Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<Type /*!*/> /*!*/
        typeParams = new List<Type /*!*/>();
      foreach (Type /*!*/ t in originalNode.TypeArguments)
      {
        Contract.Assert(t != null);
        Type /*!*/
          newType = t.Substitute(substitution.ToTypeSubst);
        Contract.Assert(newType != null);
        if (!ReferenceEquals(t, newType))
        {
          changed = true;
        }

        typeParams.Add(newType);
      }

      if (changed)
      {
        return Gen.Function(originalNode.Op, newSubExprs, typeParams);
      }
      else
      {
        return originalNode;
      }
    }

    public override VCExpr /*!*/ Visit(VCExprQuantifier /*!*/ node, VCExprSubstitution /*!*/ substitution)
    {
      Contract.Requires(node != null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      // the default is to refresh bound variables only if necessary
      // because of collisions
      return Visit(node, substitution, false);
    }

    public VCExpr /*!*/ Visit(VCExprQuantifier /*!*/ node, VCExprSubstitution /*!*/ substitution,
      bool refreshBoundVariables)
    {
      Contract.Requires(node != null);
      Contract.Requires(substitution != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      substitution.PushScope();
      try
      {
        List<TypeVariable /*!*/> /*!*/
          typeParams = node.TypeParameters;
        Contract.Assert(Cce.NonNullElements(typeParams));
        bool refreshAllVariables = refreshBoundVariables ||
                                   CollisionPossible(node.TypeParameters, node.BoundVars, substitution);
        if (refreshAllVariables)
        {
          // we introduce fresh type variables to ensure that none gets captured
          typeParams = new List<TypeVariable /*!*/>();
          foreach (TypeVariable /*!*/ var in node.TypeParameters)
          {
            Contract.Assert(var != null);
            TypeVariable /*!*/
              freshVar =
                new TypeVariable(Token.NoToken, ChooseNewVariableName(var.Name));
            Contract.Assert(freshVar != null);
            typeParams.Add(freshVar);
            substitution[var] = freshVar;
            // this might overwrite other elements of the substitution, deliberately
          }
        }

        List<VCExprVar /*!*/> /*!*/
          boundVars = node.BoundVars;
        Contract.Assert(Cce.NonNullElements(boundVars));
        if (refreshAllVariables || !substitution.TypeSubstIsEmpty)
        {
          // collisions are possible, or we also substitute type variables. in this case
          // the bound term variables have to be replaced with fresh variables with the
          // right types
          boundVars = new List<VCExprVar /*!*/>();
          IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
            typeSubst = substitution.ToTypeSubst;
          Contract.Assert(Cce.NonNullDictionaryAndValues(typeSubst));
          foreach (VCExprVar /*!*/ var in node.BoundVars)
          {
            Contract.Assert(var != null);
            VCExprVar /*!*/
              freshVar =
                Gen.Variable(ChooseNewVariableName(var.Name),
                  var.Type.Substitute(typeSubst));
            Contract.Assert(freshVar != null);
            boundVars.Add(freshVar);
            substitution[var] = freshVar;
            // this might overwrite other elements of the substitution, deliberately
          }
        }

        List<VCTrigger /*!*/> /*!*/
          newTriggers = new List<VCTrigger /*!*/>();
        foreach (VCTrigger /*!*/ trigger in node.Triggers)
        {
          Contract.Assert(trigger != null);
          newTriggers.Add(Gen.Trigger(trigger.Pos, MutateSeq(trigger.Exprs, substitution)));
        }

        VCExpr /*!*/
          newBody = Mutate(node.Body, substitution);
        Contract.Assert(newBody != null);

        return Gen.Quantify(node.Quan, typeParams, boundVars,
          newTriggers, node.Info, newBody);
      }
      finally
      {
        substitution.PopScope();
      }
    }

    public override VCExpr Visit(VCExprVar node, VCExprSubstitution substitution)
    {
      Contract.Requires(substitution != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr res = substitution[node];
      if (res != null)
      {
        return res;
      }

      return node;
    }

    public override VCExpr Visit(VCExprLet node, VCExprSubstitution substitution)
    {
      Contract.Requires(substitution != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      // the default is to refresh bound variables only if necessary
      // because of collisions
      return Visit(node, substitution, false);
    }

    public VCExpr Visit(VCExprLet node, VCExprSubstitution substitution, bool refreshBoundVariables)
    {
      Contract.Requires(substitution != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      // let-expressions do not have type parameters (fortunately ...)
      substitution.PushScope();
      try
      {
        bool refreshAllVariables =
          refreshBoundVariables ||
          !substitution.TypeSubstIsEmpty ||
          CollisionPossible(new List<TypeVariable /*!*/>(), node.BoundVars, substitution);

        List<VCExprVar /*!*/> /*!*/
          newBoundVars = node.BoundVars;
        Contract.Assert(Cce.NonNullElements(newBoundVars));
        if (refreshAllVariables)
        {
          // collisions are possible, or we also substitute type variables. in this case
          // the bound term variables have to be replaced with fresh variables with the
          // right types
          newBoundVars = new List<VCExprVar /*!*/>();
          IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
            typeSubst = substitution.ToTypeSubst;
          Contract.Assert(Cce.NonNullDictionaryAndValues(typeSubst));
          foreach (VCExprVar /*!*/ var in node.BoundVars)
          {
            Contract.Assert(var != null);
            VCExprVar /*!*/
              freshVar =
                Gen.Variable(ChooseNewVariableName(var.Name),
                  var.Type.Substitute(typeSubst));
            Contract.Assert(freshVar != null);
            newBoundVars.Add(freshVar);
            substitution[var] = freshVar;
            // this might overwrite other elements of the substitution, deliberately
          }
        }

        List<VCExprLetBinding /*!*/> /*!*/
          newbindings = new List<VCExprLetBinding /*!*/>();
        for (int i = 0; i < node.Length; ++i)
        {
          VCExprLetBinding /*!*/
            binding = node[i];
          Contract.Assert(binding != null);
          newbindings.Add(Gen.LetBinding(newBoundVars[i], Mutate(binding.E, substitution)));
        }

        VCExpr /*!*/
          newBody = Mutate(node.Body, substitution);
        Contract.Assert(newBody != null);
        return Gen.Let(newbindings, newBody);
      }
      finally
      {
        substitution.PopScope();
      }
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  [ContractClassFor(typeof(StandardVCExprOpVisitor<,>))]
  public abstract class StandardVCExprOpVisitorContracts<Result, Arg> : StandardVCExprOpVisitor<Result, Arg>
  {
    protected override Result StandardResult(VCExprNAry node, Arg arg)
    {
      Contract.Requires(node != null);
      throw new NotImplementedException();
    }
  }


  [ContractClass(typeof(StandardVCExprOpVisitorContracts<,>))]
  public abstract class StandardVCExprOpVisitor<Result, Arg>
    : IVCExprOpVisitor<Result, Arg>
  {
    protected abstract Result StandardResult(VCExprNAry /*!*/ node, Arg arg);

    public virtual Result VisitNotOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitEqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitNeqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitAndOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitOrOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitImpliesOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitDistinctOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFieldAccessOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    
    public virtual Result VisitIsConstructorOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
    
    public virtual Result VisitSelectOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitStoreOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatAddOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatSubOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatMulOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatDivOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatLeqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatLtOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatGeqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatGtOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatEqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitFloatNeqOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitBvOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitBvExtractOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitBvConcatOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitIfThenElseOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitCustomOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitAddOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitSubOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitMulOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitDivOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitModOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitRealDivOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitPowOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitLtOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitLeOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitGtOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitGeOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitSubtypeOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitSubtype3Op(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitToIntOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitToRealOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitToFloatOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }

    public virtual Result VisitBoogieFunctionOp(VCExprNAry node, Arg arg)
    {
      //Contract.Requires(node != null);
      return StandardResult(node, arg);
    }
  }
}