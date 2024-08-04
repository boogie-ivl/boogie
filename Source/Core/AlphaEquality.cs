using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class AlphaEquality : IEqualityComparer<Expr>
  {
    private readonly DeBruijnRenamer deBruijn = new DeBruijnRenamer();

    bool IEqualityComparer<Expr>.Equals(Expr x, Expr y)
    {
      var nx = deBruijn.Rename(x);
      var ny = deBruijn.Rename(y);
      return BinderExpr.EqualWithAttributesAndTriggers(nx, ny);
    }

    int IEqualityComparer<Expr>.GetHashCode(Expr obj)
    {
      return 0;
      // Best we can do because GetHashCode for Expression don't respect its equality.
      // When it does, we can instead use: 
      // return deBruijn.Rename(obj).GetHashCode(); 
    }

    // Renames expressions into deBruijn indicies, such as
    //     (lambda x : int :: x + a) 
    // into
    //     (lambda bv#0 : int :: bv#0 + fv#0) 
    // It does not handle type variables yet, but it could be added.
    //
    // This class could be made public, but it is not since the Rename method 
    // could then leak FreeVariables out of here.
    private class DeBruijnRenamer : Duplicator
    {
      // Maps from index positions and types to new variables
      private readonly TypeDict<BoundVariable> boundVars =
        new TypeDict<BoundVariable>("bv", ti => new BoundVariable(Token.NoToken, ti));

      private readonly TypeDict<FreeVariable> freeVars =
        new TypeDict<FreeVariable>("fv", ti => new FreeVariable(ti));

      // These three variables are reset at the beginning of every renaming
      private int boundVarCount, freeVarCount;
      private Dictionary<Variable, FreeVariable> freeVarMap;

      // Cached, previous results
      private readonly Dictionary<Expr, Expr> cache = new Dictionary<Expr, Expr>();

      public Expr Rename(Expr e)
      {
        if (!cache.TryGetValue(e, out var ne))
        {
          boundVarCount = 0;
          freeVarCount = 0;
          freeVarMap = new Dictionary<Variable, FreeVariable>();

          ne = VisitExpr(e);
          cache[e] = ne;
#if DEBUG_ALPHA_RENAMING
          var wr = new TokenTextWriter("<console>", options.OutputWriter, true);
          Console.Write("nm( ");
          e.Emit(wr);
          Console.WriteLine(" )");
          Console.Write("  = ");
          ne.Emit(wr);
          Console.WriteLine("");
          Console.WriteLine("h = " + ne.GetHashCode());
#endif
        }

        return ne;
      }

      public override BinderExpr VisitBinderExpr(BinderExpr node)
      {
        var subst = new Dictionary<Variable, Expr>();
        var newBound = new List<Variable>();
        foreach (var bv in node.Dummies)
        {
          var bvNew = boundVars[boundVarCount++, bv.TypedIdent.Type];
          newBound.Add(bvNew);
          subst[bv] = new IdentifierExpr(Token.NoToken, bvNew);
        }

        node.Dummies = this.VisitVariableSeq(newBound);
        node.Body = this.VisitExpr(Substituter.Apply(Substituter.SubstitutionFromDictionary(subst), node.Body));
        return node;
      }

      public override Variable VisitVariable(Variable node)
      {
        var bv = node as BoundVariable;
        if (boundVars.ContainsValue(bv))
        {
          return node;
        }
        else if (freeVarMap.TryGetValue(node, out var fv))
        {
          return fv;
        }
        else
        {
          return freeVarMap[node] = freeVars[freeVarCount++, node.TypedIdent.Type];
        }
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        var ie = (IdentifierExpr) base.VisitIdentifierExpr(node);
        // Need to fix up the name, since IdentifierExpr's equality also checks the name
        ie.Name = ie.Decl.TypedIdent.Name;
        return ie;
      }

      private class TypeDict<A>
      {
        private readonly Dictionary<Tuple<int, Type>, A> vars = new Dictionary<Tuple<int, Type>, A>();

        private readonly string Prefix; // either "bv" or "fv"
        private readonly Func<TypedIdent, A> Mk; // either new BoundVar or new FreeVar

        public TypeDict(string prefix, Func<TypedIdent, A> mk)
        {
          Prefix = prefix;
          Mk = mk;
        }

        // For debugging purposes, we create unique names when types differ, but the index are the same.
        private int created = 0;

        // Make sure that this index and this type is always mapped to the same variable
        public A this[int i, Type t]
        {
          get
          {
            if (!vars.TryGetValue(Tuple.Create(i, t), out var v))
            {
              v = Mk(new TypedIdent(Token.NoToken, Prefix + i + "#" + created++, t));
              vars[Tuple.Create(i, t)] = v;
            }

            return v;
          }
        }

        public bool ContainsValue(A a)
        {
          return vars.ContainsValue(a);
        }
      }

      private class FreeVariable : Variable
      {
        public FreeVariable(TypedIdent ti) : base(Token.NoToken, ti)
        {
        }

        public override bool IsMutable
        {
          get { throw new Cce.UnreachableException(); }
        }

        public override void Register(ResolutionContext rc)
        {
          throw new Cce.UnreachableException();
        }
      }
    }
  }
}