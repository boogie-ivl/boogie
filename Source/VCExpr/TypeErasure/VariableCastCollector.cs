using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

/// <summary>
/// Collect all variables x occurring in expressions of the form Int2U(x) or Bool2U(x), and
/// collect all variables x occurring outside such forms.
/// </summary>
internal class VariableCastCollector : TraversingVCExprVisitor<bool, bool>
{
  /// <summary>
  /// Determine those bound variables in "oldNode" <em>all</em> of whose relevant uses
  /// have to be cast in potential triggers in "newNode".  It is assume that
  /// the bound variables of "oldNode" correspond to the first bound
  /// variables of "newNode".
  /// </summary>
  public static List<VCExprVar /*!*/> /*!*/ FindCastVariables(VCExprQuantifier oldNode, VCExprQuantifier newNode,
    TypeAxiomBuilderIntBoolU axBuilder)
  {
    Contract.Requires((axBuilder != null));
    Contract.Requires((newNode != null));
    Contract.Requires((oldNode != null));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
    VariableCastCollector /*!*/
      collector = new VariableCastCollector(axBuilder);
    Contract.Assert(collector != null);
    if (newNode.Triggers.Any(trigger => trigger.Pos))
    {
      // look in the given triggers
      foreach (VCTrigger /*!*/ trigger in newNode.Triggers)
      {
        Contract.Assert(trigger != null);
        if (trigger.Pos)
        {
          foreach (VCExpr /*!*/ expr in trigger.Exprs)
          {
            Contract.Assert(expr != null);
            collector.Traverse(expr, true);
          }
        }
      }
    }
    else
    {
      // look in the body of the quantifier
      collector.Traverse(newNode.Body, true);
    }

    List<VCExprVar /*!*/> /*!*/
      castVariables = new List<VCExprVar /*!*/>(collector.varsInCasts.Count);
    foreach (VCExprVar /*!*/ castVar in collector.varsInCasts)
    {
      Contract.Assert(castVar != null);
      int i = newNode.BoundVars.IndexOf(castVar);
      if (0 <= i && i < oldNode.BoundVars.Count && !collector.varsOutsideCasts.ContainsKey(castVar))
      {
        castVariables.Add(oldNode.BoundVars[i]);
      }
    }

    return castVariables;
  }

  public VariableCastCollector(TypeAxiomBuilderIntBoolU axBuilder)
  {
    Contract.Requires(axBuilder != null);
    this.AxBuilder = axBuilder;
  }

  readonly List<VCExprVar /*!*/> /*!*/
    varsInCasts = new List<VCExprVar /*!*/>();

  readonly Dictionary<VCExprVar /*!*/, object> /*!*/
    varsOutsideCasts = new Dictionary<VCExprVar /*!*/, object>();

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullElements(varsInCasts));
    Contract.Invariant(varsOutsideCasts != null && Contract.ForAll(varsOutsideCasts, voc => voc.Key != null));
    Contract.Invariant(AxBuilder != null);
  }


  readonly TypeAxiomBuilderIntBoolU /*!*/
    AxBuilder;

  protected override bool StandardResult(VCExpr node, bool arg)
  {
    //Contract.Requires(node != null);
    return true; // not used
  }

  public override bool Visit(VCExprNAry node, bool arg)
  {
    Contract.Requires(node != null);
    if (node.Op is VCExprBoogieFunctionOp)
    {
      Function func = ((VCExprBoogieFunctionOp) node.Op).Func;
      Contract.Assert(func != null);
      if ((AxBuilder.IsCast(func)) && node[0] is VCExprVar)
      {
        VCExprVar castVar = (VCExprVar) node[0];
        if (!varsInCasts.Contains(castVar))
        {
          varsInCasts.Add(castVar);
        }

        return true;
      }
    }
    else if (node.Op is VCExprNAryOp)
    {
      VCExpressionGenerator.SingletonOp op = VCExpressionGenerator.SingletonOpDict[node.Op];
      switch (op)
      {
        // the following operators cannot be used in triggers, so disregard any uses of variables as direct arguments
        case VCExpressionGenerator.SingletonOp.NotOp:
        case VCExpressionGenerator.SingletonOp.EqOp:
        case VCExpressionGenerator.SingletonOp.NeqOp:
        case VCExpressionGenerator.SingletonOp.AndOp:
        case VCExpressionGenerator.SingletonOp.OrOp:
        case VCExpressionGenerator.SingletonOp.ImpliesOp:
        case VCExpressionGenerator.SingletonOp.LtOp:
        case VCExpressionGenerator.SingletonOp.LeOp:
        case VCExpressionGenerator.SingletonOp.GtOp:
        case VCExpressionGenerator.SingletonOp.GeOp:
          foreach (VCExpr n in node.Arguments)
          {
            if (!(n is VCExprVar))
            {
              // don't recurse on VCExprVar argument
              n.Accept<bool, bool>(this, arg);
            }
          }

          return true;
        default:
          break;
      }
    }

    return base.Visit(node, arg);
  }

  public override bool Visit(VCExprVar node, bool arg)
  {
    Contract.Requires(node != null);
    if (!varsOutsideCasts.ContainsKey(node))
    {
      varsOutsideCasts.Add(node, null);
    }

    return true;
  }
}