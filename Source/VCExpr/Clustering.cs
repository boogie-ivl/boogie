using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

// Code for managing and clustering sets of terms; this is used to
// compress the input given to the theorem prover

namespace Microsoft.Boogie.Clustering
{
  public class SubtermCollector : BoundVarTraversingVCExprVisitor<bool, bool>
  {
    private readonly VCExpressionGenerator /*!*/
      Gen;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Gen != null);
      Contract.Invariant(Cce.NonNullDictionaryAndValues(GlobalVariables));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(SubtermClusters));
    }


    public SubtermCollector(VCExpressionGenerator gen)
    {
      Contract.Requires(gen != null);
      Gen = gen;
    }

    // variables that are global and treated like constants
    private readonly IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> GlobalVariables =
      new Dictionary<VCExprVar /*!*/, VCExprVar /*!*/>();

    private readonly IDictionary<VCExprOp /*!*/, TermClustersSameHead /*!*/> SubtermClusters =
      new Dictionary<VCExprOp /*!*/, TermClustersSameHead /*!*/>();

    public void UnifyClusters()
    {
      foreach (KeyValuePair<VCExprOp /*!*/, TermClustersSameHead /*!*/> pair
        in SubtermClusters)
      {
        Contract.Assert(Cce.NonNullElements(pair));
        pair.Value.UnifyClusters();
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      //Contract.Requires(node != null);
      return false; // by default, do not collect terms containing node
    }

    public override bool Visit(VCExprLiteral node, bool arg)
    {
      Contract.Requires(node != null);
      return true;
    }

    public override bool Visit(VCExprNAry node, bool arg)
    {
      Contract.Requires(node != null);
      VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
      if (op == null)
      {
        base.Visit(node, arg);
        return false;
      }

      bool res = true;
      foreach (VCExpr subexpr in node.Arguments)
      {
        Contract.Assert(subexpr != null);
        res &= this.Traverse(subexpr, arg);
      }

      if (res)
      {
        if (!SubtermClusters.TryGetValue(op, out var clusters))
        {
          clusters = new TermClustersSameHead(op, GlobalVariables, Gen);
          SubtermClusters.Add(op, clusters);
        }

        Cce.NonNull(clusters).AddExpr(node);
      }

      return res;
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      Contract.Requires(node != null);
      if (!BoundTermVars.ContainsKey(node))
      {
        GlobalVariables[node] = node;
      }

      return true;
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      string /*!*/
        res = "";
      foreach (KeyValuePair<VCExprOp /*!*/, TermClustersSameHead /*!*/> pair
        in SubtermClusters)
      {
        Contract.Assert(Cce.NonNullElements(pair));
        res = res + pair.Value + "\n";
      }

      return res;
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // Class for managing and clustering a set of terms that all start
  // with the same function symbol
  internal class TermClustersSameHead
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Op != null);
      Contract.Invariant(Gen != null);
      Contract.Invariant(Cce.NonNullDictionaryAndValues(GlobalVariables));
    }

    // variables that are global and treated like constants
    private readonly IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/
      GlobalVariables;

    public readonly VCExprOp /*!*/
      Op;

    private readonly VCExpressionGenerator /*!*/
      Gen;

    public TermClustersSameHead(VCExprOp op, IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars,
      VCExpressionGenerator /*!*/ gen)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(globalVars));
      Contract.Requires(gen != null);
      Contract.Requires(op != null);
      Op = op;
      GlobalVariables = globalVars;
      Gen = gen;
    }

    private readonly List<Cluster> /*!*/
      Clusters = new List<Cluster>();

    private struct Cluster
    {
      public readonly VCExprNAry /*!*/
        Generator;

      public readonly int Size;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Generator != null);
      }

      public Cluster(VCExprNAry generator, int size)
      {
        Contract.Requires(generator != null);
        Generator = generator;
        Size = size;
      }
    }

    private int Distance(Cluster a, Cluster b)
    {
      AntiUnificationVisitor /*!*/
        visitor = new AntiUnificationVisitor(Gen);
      visitor.AntiUnify(a.Generator, b.Generator);

      visitor.RepresentationSize(GlobalVariables, out var reprSizeA, out var reprSizeB);
      return (a.Size - 1) * reprSizeA + (b.Size - 1) * reprSizeB;
    }

    private bool EqualUpToRenaming(Cluster a, Cluster b)
    {
      AntiUnificationVisitor /*!*/
        visitor = new AntiUnificationVisitor(Gen);
      visitor.AntiUnify(a.Generator, b.Generator);
      return visitor.RepresentationIsRenaming(GlobalVariables);
    }

    private Cluster Merge(Cluster a, Cluster b)
    {
      AntiUnificationVisitor /*!*/
        visitor = new AntiUnificationVisitor(Gen);
      VCExpr /*!*/
        generator = visitor.AntiUnify(a.Generator, b.Generator);
      Contract.Assert(generator != null);
      VCExprNAry generatorNAry = generator as VCExprNAry;
      Contract.Assert(generatorNAry != null && Op.Equals(generatorNAry.Op));
      return new Cluster(generatorNAry, a.Size + b.Size);
    }

    ////////////////////////////////////////////////////////////////////////////

    public void AddExpr(VCExprNAry expr)
    {
      Contract.Requires(expr != null);
      Contract.Requires(Op.Equals(expr.Op));

      Cluster c = new Cluster(expr, 1);
      for (int i = 0; i < Clusters.Count; ++i)
      {
        Cluster d = Clusters[i];
        if (EqualUpToRenaming(c, d))
        {
          Clusters[i] = new Cluster(d.Generator, d.Size + 1);
          return;
        }
      }

      Clusters.Add(c);
    }

    ////////////////////////////////////////////////////////////////////////////

    private struct ClusteringMatrix
    {
      private readonly VCExpressionGenerator /*!*/
        Gen;

      private readonly IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/
        GlobalVariables;

      public readonly List<Cluster> /*!*/
        Clusters;

      public readonly bool[] /*!*/
        RemainingClusters;

      public readonly Distance[,] /*!*/
        Distances;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Gen != null);
        Contract.Invariant(Cce.NonNullDictionaryAndValues(GlobalVariables));
        Contract.Invariant(Clusters != null);
        Contract.Invariant(RemainingClusters != null);
        Contract.Invariant(Distances != null);
      }


      public struct Distance
      {
        public readonly int Dist;

        public readonly VCExprNAry /*!*/
          Generator;

        public Distance(Cluster a, Cluster b, IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars,
          VCExpressionGenerator gen)
        {
          Contract.Requires(gen != null);
          Contract.Requires(Cce.NonNullDictionaryAndValues(globalVars));
          AntiUnificationVisitor /*!*/
            visitor = new AntiUnificationVisitor(gen);
          Generator = (VCExprNAry) visitor.AntiUnify(a.Generator, b.Generator);

          visitor.RepresentationSize(globalVars, out var reprSizeA, out var reprSizeB);
          Dist = (a.Size - 1) * reprSizeA + (b.Size - 1) * reprSizeB;
        }
      }

      public ClusteringMatrix(List<Cluster> clusters, IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars,
        VCExpressionGenerator gen)
      {
        Contract.Requires(gen != null);
        Contract.Requires(clusters != null);
        Contract.Requires(Cce.NonNullDictionaryAndValues(globalVars));
        List<Cluster> c = new List<Cluster>();
        c.AddRange(clusters);
        Clusters = c;

        GlobalVariables = globalVars;
        Gen = gen;

        bool[] remaining = new bool[clusters.Count];
        RemainingClusters = remaining;
        for (int i = 0; i < remaining.Length; ++i)
        {
          remaining[i] = true;
        }

        Distance[,] /*!*/
          distances = new Distance[clusters.Count, clusters.Count];
        Distances = distances;
        for (int i = 1; i < clusters.Count; ++i)
        {
          for (int j = 0; j < i; ++j)
          {
            distances[i, j] =
            new Distance(clusters[i], clusters[j], GlobalVariables, Gen);
          }
        }
      }

      public void UnifyClusters(int maxDist)
      {
        while (true)
        {
          int minDist = FindMinDistance(out var i, out var j);

          if (minDist > maxDist)
          {
            return;
          }

          MergeClusters(i, j);
        }
      }

      public void ResultingClusters(List<Cluster> clusters)
      {
        Contract.Requires(clusters != null);
        clusters.Clear();
        for (int i = 0; i < Clusters.Count; ++i)
        {
          if (RemainingClusters[i])
          {
            clusters.Add(Clusters[i]);
          }
        }
      }

      //////////////////////////////////////////////////////////////////////////

      private void Update(int i)
      {
        for (int j = 0; j < i; ++j)
        {
          if (RemainingClusters[j])
          {
            Distances[i, j] =
              new Distance(Clusters[i], Clusters[j], GlobalVariables, Gen);
          }
        }

        for (int j = i + 1; j < Clusters.Count; ++j)
        {
          if (RemainingClusters[j])
          {
            Distances[j, i] =
              new Distance(Clusters[j], Clusters[i], GlobalVariables, Gen);
          }
        }
      }

      private int FindMinDistance(out int c0, out int c1)
      {
        int minDist = int.MaxValue;
        c0 = -1;
        c1 = -1;

        for (int i = 0; i < Clusters.Count; ++i)
        {
          if (RemainingClusters[i])
          {
            for (int j = 0; j < i; ++j)
            {
              if (RemainingClusters[j])
              {
                if (Distances[i, j].Dist < minDist)
                {
                  minDist = Distances[i, j].Dist;
                  c0 = i;
                  c1 = j;
                }
              }
            }
          }
        }

        Contract.Assert(c0 == -1 && c1 == -1 || c0 > c1 && c1 >= 0);
        return minDist;
      }

      private void MergeClusters(int i, int j)
      {
        Contract.Requires(j >= 0 && i > j && RemainingClusters[i] && RemainingClusters[j]);
        Clusters[i] = new Cluster(Distances[i, j].Generator,
          Clusters[i].Size + Clusters[j].Size);
        RemainingClusters[j] = false;
        Update(i);
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    public void UnifyClusters()
    {
      ClusteringMatrix matrix =
        new ClusteringMatrix(Clusters, GlobalVariables, Gen);
      matrix.UnifyClusters(50);
      matrix.ResultingClusters(Clusters);
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      string /*!*/
        res = "";
      foreach (Cluster c in Clusters)
      {
        res = res + c.Generator + "\t" + c.Size + "\n";
      }

      return res;
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  internal class AntiUnificationVisitor : TraversingVCExprVisitor<VCExpr /*!*/, VCExpr /*!*/>
  {
    private readonly VCExpressionGenerator /*!*/
      Gen;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Gen != null);
      Contract.Invariant(Cce.NonNullDictionaryAndValues(Representation));
    }


    public AntiUnificationVisitor(VCExpressionGenerator gen)
    {
      Contract.Requires(gen != null);
      Gen = gen;
    }

    // Sub-expressions in the first and second expression to be
    // anti-unified that are replaced with variables
    private readonly IDictionary<ExprPair, VCExprVar /*!*/> /*!*/
      Representation =
        new Dictionary<ExprPair, VCExprVar /*!*/>();


    private struct ExprPair
    {
      public readonly VCExpr /*!*/
        Expr0, Expr1;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Expr0 != null);
        Contract.Invariant(Expr1 != null);
      }

      public ExprPair(VCExpr expr0, VCExpr expr1)
      {
        Contract.Requires(expr1 != null);
        Contract.Requires(expr0 != null);
        Expr0 = expr0;
        Expr1 = expr1;
      }

      [Pure]
      [Reads(ReadsAttribute.Reads.Nothing)]
      public override bool Equals(object that)
      {
        if (that is ExprPair)
        {
          ExprPair thatPair = (ExprPair) that;
          return this.Expr0.Equals(thatPair.Expr0) &&
                 this.Expr1.Equals(thatPair.Expr1);
        }

        return false;
      }

      [Pure]
      public override int GetHashCode()
      {
        return Expr0.GetHashCode() + Expr1.GetHashCode() * 13;
      }
    }

    public void Reset()
    {
      Representation.Clear();
    }

    public bool RepresentationIsRenaming(IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(globalVars));
      if (!Representation.Any(pair =>
        pair.Key.Expr0 is VCExprVar && pair.Key.Expr1 is VCExprVar &&
        !globalVars.ContainsKey(Cce.NonNull((VCExprVar) pair.Key.Expr0)) &&
        !globalVars.ContainsKey(Cce.NonNull((VCExprVar /*!*/) pair.Key.Expr1))))
      {
        return false;
      }
      // check that all substituted variables are distinct
      // TODO: optimise
      return
        Representation.All(pair1 => Representation.All(pair2 =>
          pair1.Value.Equals(pair2.Value) ||
          !pair1.Key.Expr0.Equals(pair2.Key.Expr0) && !pair1.Key.Expr1.Equals(pair2.Key.Expr1)));
    }

    public void RepresentationSize(IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars, out int expr0Size,
      out int expr1Size)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(globalVars));
      ReprSizeComputingVisitor /*!*/
        size0Visitor = new ReprSizeComputingVisitor();
      ReprSizeComputingVisitor /*!*/
        size1Visitor = new ReprSizeComputingVisitor();

      foreach (KeyValuePair<ExprPair, VCExprVar /*!*/> pair in Representation)
      {
        Contract.Assert(pair.Value != null);
        size0Visitor.ComputeSize(pair.Key.Expr0, globalVars);
        size1Visitor.ComputeSize(pair.Key.Expr1, globalVars);
      }

      expr0Size = size0Visitor.Size;
      expr1Size = size1Visitor.Size;
    }

    public VCExpr AntiUnify(VCExpr s, VCExpr t)
    {
      Contract.Requires(t != null);
      Contract.Requires(s != null);
      Contract.Requires((s.Type.Equals(t.Type)));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Traverse(s, t);
    }

    ////////////////////////////////////////////////////////////////////////////

    private VCExprVar AbstractWithVariable(VCExpr s, VCExpr t)
    {
      Contract.Requires(t != null);
      Contract.Requires(s != null);
      Contract.Requires((s.Type.Equals(t.Type)));
      Contract.Ensures(Contract.Result<VCExprVar>() != null);

      ExprPair pair = new ExprPair(s, t);
      if (!Representation.TryGetValue(pair, out var repr))
      {
        repr = Gen.Variable("abs" + Representation.Count, s.Type);
        Representation.Add(pair, repr);
      }

      return Cce.NonNull(repr);
    }

    ////////////////////////////////////////////////////////////////////////////

    public override VCExpr Visit(VCExprLiteral node, VCExpr that)
    {
      Contract.Requires(that != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (node.Equals(that))
      {
        return node;
      }

      return AbstractWithVariable(node, that);
    }

    public override VCExpr Visit(VCExprNAry node, VCExpr that)
    {
      Contract.Requires(that != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExprNAry thatNAry = that as VCExprNAry;
      if (thatNAry != null && node.Op.Equals(thatNAry.Op))
      {
        // type parameters should already have been eliminated at this
        // stage
        Contract.Assert(node.TypeParamArity == 0 && thatNAry.TypeParamArity == 0 && node.Arity == thatNAry.Arity);

        List<VCExpr /*!*/> /*!*/
          unifiedArgs = new List<VCExpr /*!*/>();
        for (int i = 0; i < node.Arity; ++i)
        {
          unifiedArgs.Add(Traverse(node[i], thatNAry[i]));
        }

        return Gen.Function(node.Op, unifiedArgs);
      }

      return AbstractWithVariable(node, that);
    }

    public override VCExpr Visit(VCExprVar node, VCExpr that)
    {
      Contract.Requires(that != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (node.Equals(that))
      {
        return node;
      }

      return AbstractWithVariable(node, that);
    }

    protected override VCExpr StandardResult(VCExpr node, VCExpr that)
    {
      //Contract.Requires(that != null);
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException(); // not handled here      
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  internal class ReprSizeComputingVisitor
    : TraversingVCExprVisitor<bool,
      // variables considered as global constants
      IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/>
  {
    public int Size = 0;

    public void ComputeSize(VCExpr expr, IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars)
    {
      Contract.Requires(expr != null);
      Contract.Requires(Cce.NonNullDictionaryAndValues(globalVars));
      Traverse(expr, globalVars);
    }

    protected override bool StandardResult(VCExpr node, IDictionary<VCExprVar /*!*/, VCExprVar /*!*/> /*!*/ globalVars)
    {
      //Contract.Requires(node != null);
      //Contract.Requires(cce.NonNullElements(globalVars));
      VCExprVar nodeAsVar = node as VCExprVar;
      if (nodeAsVar == null || globalVars.ContainsKey(nodeAsVar))
      {
        Size = Size + 1;
      }

      return true;
    }
  }
}