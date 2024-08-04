using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

// Sort the bindings in a let-expression so that terms bound earlier do
// not contain variables bound later

namespace Microsoft.Boogie.VCExprAST
{
  // (argument is not used)
  public class LetBindingSorter : MutatingVCExprVisitor<bool>
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(FreeVarCollector != null);
    }

    private readonly FreeVariableCollector /*!*/
      FreeVarCollector =
        new FreeVariableCollector();

    private List<VCExprVar /*!*/> /*!*/ FreeVarsIn(VCExpr expr)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
      FreeVarCollector.Collect(expr);
      List<VCExprVar /*!*/> /*!*/
        freeVars = new List<VCExprVar /*!*/>(FreeVarCollector.FreeTermVars);
      FreeVarCollector.Reset();
      return freeVars;
    }

    public LetBindingSorter(VCExpressionGenerator gen) : base(gen)
    {
      Contract.Requires(gen != null);
    }

    public override VCExpr Visit(VCExprLet node, bool arg)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      IDictionary<VCExprVar /*!*/, Binding /*!*/> boundVars =
        new Dictionary<VCExprVar /*!*/, Binding /*!*/>();

      // recurse and collect the free variables in bound terms and formulae
      foreach (VCExprLetBinding /*!*/ binding in node)
      {
        Contract.Assert(binding != null);
        VCExpr /*!*/
          newE = Mutate(binding.E, arg);
        Binding /*!*/
          b = new Binding(binding.V, newE, FreeVarsIn(newE));
        boundVars.Add(b.V, b);
      }

      // generate the occurrence edges
      foreach (KeyValuePair<VCExprVar /*!*/, Binding /*!*/> pair in boundVars)
      {
        Contract.Assert(Cce.NonNullElements(pair));
        Binding /*!*/
          b = pair.Value;
        Contract.Assert(b != null);
        foreach (VCExprVar /*!*/ v in b.FreeVars)
        {
          Contract.Assert(v != null);
          if (boundVars.TryGetValue(v, out var b2))
          {
            Cce.NonNull(b2).Occurrences.Add(b);
            b.InvOccurrencesNum = b.InvOccurrencesNum + 1;
          }
        }
      }

      // topological sort
      Stack<Binding /*!*/> rootBindings = new Stack<Binding /*!*/>();
      foreach (KeyValuePair<VCExprVar /*!*/, Binding /*!*/> pair in boundVars)
      {
        Contract.Assert(Cce.NonNullElements(pair));
        if (pair.Value.InvOccurrencesNum == 0)
        {
          rootBindings.Push(pair.Value);
        }
      }

      List<Binding /*!*/> /*!*/
        sortedBindings = new List<Binding /*!*/>();
      while (rootBindings.Count > 0)
      {
        Binding /*!*/
          b = rootBindings.Pop();
        Contract.Assert(b != null);
        sortedBindings.Add(b);
        foreach (Binding /*!*/ b2 in b.Occurrences)
        {
          Contract.Assert(b2 != null);
          b2.InvOccurrencesNum = b2.InvOccurrencesNum - 1;
          if (b2.InvOccurrencesNum == 0)
          {
            rootBindings.Push(b2);
          }
        }
      }

      if (boundVars.Any(pair => pair.Value.InvOccurrencesNum > 0))
      {
        System.Diagnostics.Debug.Fail("Cyclic let-bindings");
      }

      Contract.Assert(node.Length == sortedBindings.Count);

      // check which of the bindings can be dropped
      VCExpr newBody = Mutate(node.Body, arg);
      Contract.Assert(newBody != null);

      IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/
        usedVars =
          new Dictionary<VCExprVar /*!*/, VCExprVar /*!*/>();
      foreach (VCExprVar /*!*/ v in FreeVarsIn(newBody))
      {
        Contract.Assert(v != null);
        if (!usedVars.ContainsKey(v))
        {
          usedVars.Add(v, v);
        }
      }

      for (int i = sortedBindings.Count - 1; i >= 0; --i)
      {
        if (usedVars.ContainsKey(sortedBindings[i].V))
        {
          foreach (VCExprVar /*!*/ v in sortedBindings[i].FreeVars)
          {
            Contract.Assert(v != null);
            if (!usedVars.ContainsKey(v))
            {
              usedVars.Add(v, v);
            }
          }
        }
        else
        {
          sortedBindings.RemoveAt(i);
        }
      }

      // assemble the resulting let-expression
      List<VCExprLetBinding /*!*/> /*!*/
        newBindings = new List<VCExprLetBinding /*!*/>();
      foreach (Binding b in sortedBindings)
      {
        newBindings.Add(Gen.LetBinding(b.V, b.E));
      }

      return Gen.Let(newBindings, newBody);
    }

    private class Binding
    {
      public readonly VCExprVar /*!*/
        V;

      public readonly VCExpr /*!*/
        E;

      public readonly List<VCExprVar /*!*/> /*!*/
        FreeVars;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(V != null);
        Contract.Invariant(E != null);
        Contract.Invariant(Cce.NonNullElements(FreeVars));
        Contract.Invariant(Occurrences != null);
      }


      // list of all bound expression in which the variable V occurs
      // (outgoing edges)
      public readonly List<Binding> /*!*/
        Occurrences;

      // number of variables that are bound in this let-expression
      // and that occur in FreeVars
      // (incoming edges)
      public int InvOccurrencesNum;

      public Binding(VCExprVar v, VCExpr e, List<VCExprVar /*!*/> /*!*/ freeVars)
      {
        Contract.Requires(e != null);
        Contract.Requires(v != null);
        Contract.Requires(Cce.NonNullElements(freeVars));
        this.V = v;
        this.E = e;
        this.FreeVars = freeVars;
        this.Occurrences = new List<Binding>();
        this.InvOccurrencesNum = 0;
      }
    }
  }
}