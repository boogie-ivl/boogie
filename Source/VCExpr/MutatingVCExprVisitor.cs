using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST;

public abstract class MutatingVCExprVisitor<Arg>
  : IVCExprVisitor<VCExpr /*!*/, Arg>
{
  protected readonly VCExpressionGenerator /*!*/
    Gen;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Gen != null);
  }
    
  public MutatingVCExprVisitor(VCExpressionGenerator gen)
  {
    Contract.Requires(gen != null);
    this.Gen = gen;
  }

  public VCExpr Mutate(VCExpr expr, Arg arg)
  {
    Contract.Requires(expr != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return expr.Accept(this, arg);
  }

  public List<VCExpr /*!*/> /*!*/ MutateSeq(IEnumerable<VCExpr /*!*/> /*!*/ exprs, Arg arg)
  {
    Contract.Requires(Cce.NonNullElements(exprs));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
    List<VCExpr /*!*/> /*!*/
      res = new List<VCExpr /*!*/>();
    foreach (VCExpr /*!*/ expr in exprs)
    {
      Contract.Assert(expr != null);
      res.Add(expr.Accept(this, arg));
    }

    return res;
  }

  private List<VCExpr /*!*/> /*!*/ MutateList(List<VCExpr /*!*/> /*!*/ exprs, Arg arg)
  {
    Contract.Requires(Cce.NonNullElements(exprs));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
    bool changed = false;
    List<VCExpr /*!*/> /*!*/
      res = new List<VCExpr /*!*/>();
    foreach (VCExpr /*!*/ expr in exprs)
    {
      Contract.Assert(expr != null);
      VCExpr /*!*/
        newExpr = expr.Accept(this, arg);
      if (!Object.ReferenceEquals(expr, newExpr))
      {
        changed = true;
      }

      res.Add(newExpr);
    }

    if (!changed)
    {
      return exprs;
    }

    return res;
  }

  public virtual VCExpr Visit(VCExprLiteral node, Arg arg)
  {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return node;
  }

  ////////////////////////////////////////////////////////////////////////////

  // Special element used to mark the positions in the todo-stack where
  // results have to be popped from the result-stack.
  private static readonly VCExpr /*!*/
    CombineResultsMarker = new VCExprLiteral(Type.Bool);

  // The todo-stack contains records of the shape
  //
  //     arg0
  //     arg1
  //     arg2
  //     ...
  //     CombineResultsMarker
  //     f(arg0, arg1, arg2, ...)               (the original expression)

  private readonly Stack<VCExpr /*!*/> /*!*/
    NAryExprTodoStack = new Stack<VCExpr /*!*/>();

  private readonly Stack<VCExpr /*!*/> /*!*/
    NAryExprResultStack = new Stack<VCExpr /*!*/>();

  [ContractInvariantMethod]
  void ObjectInvarianta()
  {
    Contract.Invariant(Cce.NonNullElements(NAryExprResultStack));
    Contract.Invariant(Cce.NonNullElements(NAryExprTodoStack));
  }


  private void PushTodo(VCExprNAry exprTodo)
  {
    Contract.Requires(exprTodo != null);
    NAryExprTodoStack.Push(exprTodo);
    NAryExprTodoStack.Push(CombineResultsMarker);
    for (int i = exprTodo.Arity - 1; i >= 0; --i)
    {
      NAryExprTodoStack.Push(exprTodo[i]);
    }
  }

  public virtual bool AvoidVisit(VCExprNAry node, Arg arg)
  {
    return true;
  }

  public virtual VCExpr Visit(VCExprNAry node, Arg arg)
  {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    int initialStackSize = NAryExprTodoStack.Count;
    int initialResultStackSize = NAryExprResultStack.Count;

    PushTodo(node);

    while (NAryExprTodoStack.Count > initialStackSize)
    {
      VCExpr /*!*/
        subExpr = NAryExprTodoStack.Pop();
      Contract.Assert(subExpr != null);

      if (Object.ReferenceEquals(subExpr, CombineResultsMarker))
      {
        // assemble a result
        VCExprNAry /*!*/
          originalExpr = (VCExprNAry) NAryExprTodoStack.Pop();
        Contract.Assert(originalExpr != null);
        VCExprOp /*!*/
          op = originalExpr.Op;
        bool changed = false;
        List<VCExpr /*!*/> /*!*/
          newSubExprs = new List<VCExpr /*!*/>();

        for (int i = op.Arity - 1; i >= 0; --i)
        {
          VCExpr /*!*/
            nextSubExpr = NAryExprResultStack.Pop();
          Contract.Assert(nextSubExpr != null);
          if (!Object.ReferenceEquals(nextSubExpr, originalExpr[i]))
          {
            changed = true;
          }

          newSubExprs.Insert(0, nextSubExpr);
        }

        NAryExprResultStack.Push(UpdateModifiedNode(originalExpr, newSubExprs, changed, arg));
        //
      }
      else
      {
        //
        VCExprNAry narySubExpr = subExpr as VCExprNAry;
        if (narySubExpr != null && this.AvoidVisit(narySubExpr, arg) &&
            // as in VCExprNAryUniformOpEnumerator, all expressions with
            // type parameters are allowed to be inspected more closely
            narySubExpr.TypeParamArity == 0)
        {
          PushTodo(narySubExpr);
        }
        else
        {
          NAryExprResultStack.Push(subExpr.Accept(this, arg));
        }

        //
      }
    }

    Contract.Assert(NAryExprTodoStack.Count == initialStackSize &&
                    NAryExprResultStack.Count == initialResultStackSize + 1);
    return NAryExprResultStack.Pop();
  }

  protected virtual VCExpr /*!*/ UpdateModifiedNode(VCExprNAry /*!*/ originalNode,
    List<VCExpr /*!*/> /*!*/ newSubExprs, // has any of the subexpressions changed? 
    bool changed,
    Arg arg)
  {
    Contract.Requires(Cce.NonNullElements(newSubExprs));
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    if (changed)
    {
      return Gen.Function(originalNode.Op,
        newSubExprs, originalNode.TypeArguments);
    }
    else
    {
      return originalNode;
    }
  }

  ////////////////////////////////////////////////////////////////////////////

  public virtual VCExpr Visit(VCExprVar node, Arg arg)
  {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    return node;
  }

  protected List<VCTrigger /*!*/> /*!*/ MutateTriggers(List<VCTrigger /*!*/> /*!*/ triggers, Arg arg)
  {
    Contract.Requires(Cce.NonNullElements(triggers));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCTrigger>>()));
    List<VCTrigger /*!*/> /*!*/
      newTriggers = new List<VCTrigger /*!*/>();
    bool changed = false;
    foreach (VCTrigger /*!*/ trigger in triggers)
    {
      Contract.Assert(trigger != null);
      List<VCExpr /*!*/> /*!*/
        exprs = trigger.Exprs;
      List<VCExpr /*!*/> /*!*/
        newExprs = MutateList(exprs, arg);

      if (Object.ReferenceEquals(exprs, newExprs))
      {
        newTriggers.Add(trigger);
      }
      else
      {
        newTriggers.Add(Gen.Trigger(trigger.Pos, newExprs));
        changed = true;
      }
    }

    if (!changed)
    {
      return triggers;
    }

    return newTriggers;
  }

  public virtual VCExpr Visit(VCExprQuantifier node, Arg arg)
  {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    bool changed = false;

    VCExpr /*!*/
      body = node.Body;
    Contract.Assert(body != null);
    VCExpr /*!*/
      newbody = body.Accept(this, arg);
    Contract.Assert(newbody != null);
    if (!Object.ReferenceEquals(body, newbody))
    {
      changed = true;
    }

    // visit the trigger expressions as well
    List<VCTrigger /*!*/> /*!*/
      triggers = node.Triggers;
    Contract.Assert(Cce.NonNullElements(triggers));
    List<VCTrigger /*!*/> /*!*/
      newTriggers = MutateTriggers(triggers, arg);
    Contract.Assert(Cce.NonNullElements(newTriggers));
    if (!Object.ReferenceEquals(triggers, newTriggers))
    {
      changed = true;
    }

    if (!changed)
    {
      return node;
    }

    return Gen.Quantify(node.Quan, node.TypeParameters, node.BoundVars,
      newTriggers, node.Info, newbody);
  }

  public virtual VCExpr Visit(VCExprLet node, Arg arg)
  {
    //Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    bool changed = false;

    VCExpr /*!*/
      body = node.Body;
    VCExpr /*!*/
      newbody = body.Accept(this, arg);
    if (!Object.ReferenceEquals(body, newbody))
    {
      changed = true;
    }

    List<VCExprLetBinding /*!*/> /*!*/
      newbindings = new List<VCExprLetBinding /*!*/>();
    for (int i = 0; i < node.Length; ++i)
    {
      VCExprLetBinding /*!*/
        binding = node[i];
      Contract.Assert(binding != null);
      VCExpr /*!*/
        e = binding.E;
      VCExpr /*!*/
        newE = e.Accept(this, arg);
      if (Object.ReferenceEquals(e, newE))
      {
        newbindings.Add(binding);
      }
      else
      {
        changed = true;
        newbindings.Add(Gen.LetBinding(binding.V, newE));
      }
    }

    if (!changed)
    {
      return node;
    }

    return Gen.Let(newbindings, newbody);
  }
}