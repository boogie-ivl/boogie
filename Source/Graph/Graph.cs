using System;
using System.Linq;
using System.Collections.Generic;
using System.Text; // for StringBuilder
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.GraphUtil
{
  internal static class Util
  {
    private static string /*!*/ ListToString<T>(IEnumerable<T> xs)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      sb.Append("[");
      bool first = true;
      foreach (T /*!*/ x in xs)
      {
        Contract.Assert(x != null);
        if (!first)
        {
          sb.Append(", ");
        }

        sb.Append(x.ToString());
        first = false;
      }

      sb.Append("]");
      return sb.ToString();
    }

    public static string /*!*/ MapToString<Node>(Dictionary<Node, List<Node>> d)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      sb.Append("{");
      bool first = true;
      foreach (KeyValuePair<Node, List<Node>> de in d)
      {
        if (!first)
        {
          sb.Append(", ");
        }

        Contract.Assert(!object.Equals(de.Key, default(Node)));
        sb.Append(de.Key.ToString());
        sb.Append("~>");
        sb.Append(ListToString(de.Value));
        first = false;
      }

      sb.Append("}");
      return sb.ToString();
    }
  }

  public class DomRelation<Node>
  {
    // doms maps (unique) node numbers to the node numbers of the immediate dominator
    // to use it on Nodes, one needs the two way mapping between nodes and their numbers.
    private int[] doms; // 0 is unused: means undefined

    // here are the two mappings
    private Node[] postOrderNumberToNode;
    private Dictionary<Node, int> nodeToPostOrderNumber;
    private int sourceNum; // (number for) root of the graph
    private Node source; // root of the graph
    private Graph<Node> graph;
    private Dictionary<Node, List<Node>> immediateDominatorMap;

    [NotDelayed]
    internal DomRelation(Graph<Node> g, Node source)
    {
      this.graph = g;
      // slot 0 not used: nodes are numbered from 1 to n so zero
      // can represent undefined.
      this.source = source;
      //:base();
      this.NewComputeDominators();
    }

    public Dictionary<Node, List<Node>> ImmediateDominatorMap
    {
      get
      {
        Contract.Assume(this.immediateDominatorMap != null);
        return this.immediateDominatorMap;
      }
    }

    public bool DominatedBy(Node dominee, Node dominator, List<Node> path = null)
    {
      Contract.Assume(this.nodeToPostOrderNumber != null);
      Contract.Assume(this.doms != null);
      int domineeNum = this.nodeToPostOrderNumber[dominee];
      int dominatorNum = this.nodeToPostOrderNumber[dominator];
      if (domineeNum == dominatorNum)
      {
        return true;
      }

      int currentNodeNum = this.doms[domineeNum];
      while (true)
      {
        if (currentNodeNum == dominatorNum)
        {
          return true;
        }

        if (currentNodeNum == this.sourceNum)
        {
          return false;
        }

        if (path != null)
        {
          path.Add(postOrderNumberToNode[currentNodeNum]);
        }

        currentNodeNum = this.doms[currentNodeNum];
      }
    }

    private Dictionary<Node, List<Node>> domMap = null;

    [Pure]
    public override string ToString()
    {
      Contract.Assume(this.doms != null);
      int[] localDoms = this.doms;
      Contract.Assume(this.postOrderNumberToNode != null);
      if (domMap == null)
      {
        domMap = new Dictionary<Node, List<Node>>();
        for (int i = 1; i < localDoms.Length; i++)
        {
          // 0 slot is not used
          int domineeNum = i;
          int currentNodeNum = domineeNum;
          List<Node> dominators = new List<Node>();
          while (currentNodeNum != this.sourceNum)
          {
            dominators.Add(this.postOrderNumberToNode[currentNodeNum]);
            currentNodeNum = this.doms[currentNodeNum];
          }

          dominators.Add(this.postOrderNumberToNode[this.sourceNum]);
          domMap.Add(this.postOrderNumberToNode[i], dominators);
        }
      }

      StringBuilder sb = new StringBuilder();
      sb.Append("{");
      bool first = true;
      foreach (KeyValuePair<Node, List<Node>> de in domMap)
      {
        if (!first)
        {
          sb.Append(", ");
        }

        Contract.Assert(!object.Equals(de.Key, default(Node)));
        sb.Append(de.Key.ToString());
        sb.Append("~>");
        sb.Append(ListToString(de.Value));
        first = false;
      }

      sb.Append("}");
      return sb.ToString();
    }

    private void PrintIntArray(int[] xs)
    {
      Console.Write("[");
      for (int i = 0; i < xs.Length; i++)
      {
        if (0 < i)
        {
          Console.Write(", ");
        }

        Console.Write(xs[i]);
      }

      Console.WriteLine("]");
    }

    public void PrintList<T>(IEnumerable<T> xs)
    {
      Console.Write("[");
      int i = 0;
      foreach (T /*!*/ x in xs)
      {
        Contract.Assert(x != null);
        if (0 < i)
        {
          Console.Write(", ");
        }

        Console.Write(x.ToString());
        i++;
      }

      Console.WriteLine("]");
    }

    public string /*!*/ ListToString<T>(IEnumerable<T> xs)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      StringBuilder sb = new StringBuilder();
      sb.Append("[");
      bool first = true;
      foreach (T /*!*/ x in xs)
      {
        Contract.Assert(x != null);
        if (!first)
        {
          sb.Append(", ");
        }

        sb.Append(x.ToString());
        first = false;
      }

      sb.Append("]");
      return sb.ToString();
    }

    // Keith D. Cooper, Timothy J. Harvey, Ken Kennedy, "A Simple, Fast Dominance Algorithm ", Software Practice and Experience, 2001.
    // http://citeseer.ist.psu.edu/cooper01simple.html
    private void NewComputeDominators()
    {
      int n = this.graph.Nodes.Count;
      this.postOrderNumberToNode = new Node[n + 1];
      this.nodeToPostOrderNumber = new Dictionary<Node, int>();
      //HashSet<Node> visited = new HashSet<Node>();
      //int currentNumber = 1;
      Contract.Assume(this.source != null);
      //this.PostOrderVisit(this.source, visited, ref currentNumber);
      this.PostOrderVisitIterative(this.source);
      this.sourceNum = this.nodeToPostOrderNumber[source];
      //    for (int i = 1; i <= n; i++){ Console.WriteLine(postOrderNumberToNode[i]); }
      this.doms = new int[n + 1]; // 0 is unused: means undefined
      Node start_node = this.source;
      this.doms[this.nodeToPostOrderNumber[start_node]] = this.nodeToPostOrderNumber[start_node];
      bool changed = true;
      //    PrintIntArray(doms);
      while (changed)
      {
        changed = false;
        // for all nodes, b, in reverse postorder (except start_node)
        for (int nodeNum = n - 1; 1 <= nodeNum; nodeNum--)
        {
          Node b = this.postOrderNumberToNode[nodeNum];
          IEnumerable<Node> predecessors = this.graph.Predecessors(b);
          // find a predecessor (i.e., a higher number) for which
          // the doms array has been set
          int new_idom = 0;
          int first_processed_predecessor = 0;

          #region new_idom <- number of first (processed) predecessor of b (pick one)

          foreach (Node p in predecessors)
          {
            if (this.doms[this.nodeToPostOrderNumber[p]] != 0)
            {
              int x = this.nodeToPostOrderNumber[p];
              new_idom = x;
              first_processed_predecessor = x;
              break;
            }
          }

          #endregion

          #region for all other predecessors, p, of b

          foreach (Node p in predecessors)
          {
            if (this.nodeToPostOrderNumber[p] == first_processed_predecessor)
            {
              continue;
            }

            if (this.doms[this.nodeToPostOrderNumber[p]] != 0)
            {
              new_idom = intersect(this.nodeToPostOrderNumber[p], new_idom, this.doms);
            }
          }

          #endregion

          if (this.doms[this.nodeToPostOrderNumber[b]] != new_idom)
          {
            this.doms[this.nodeToPostOrderNumber[b]] = new_idom;
            changed = true;
          }
        }
      }

      #region Populate the Immediate Dominator Map

      int sourceNum = this.nodeToPostOrderNumber[this.source];
      immediateDominatorMap = new Dictionary<Node, List<Node>>();
      for (int i = 1; i <= n; i++)
      {
        Node node = this.postOrderNumberToNode[i];
        Node idomNode = this.postOrderNumberToNode[this.doms[i]];
        if (i == sourceNum && this.doms[i] == sourceNum)
        {
          continue;
        }

        if (immediateDominatorMap.ContainsKey(idomNode))
        {
          immediateDominatorMap[idomNode].Add(node);
        }
        else
        {
          List<Node> l = new List<Node>();
          l.Add(node);
          immediateDominatorMap.Add(idomNode, l);
        }
      }

      #endregion
    }

    private int intersect(int b1, int b2, int[] doms)
    {
      int finger1 = b1;
      int finger2 = b2;
      while (finger1 != finger2)
      {
        while (finger1 < finger2)
        {
          finger1 = doms[finger1];
        }

        while (finger2 < finger1)
        {
          finger2 = doms[finger2];
        }
      }

      return finger1;
    }

    private void PostOrderVisit(Node /*!*/ n, HashSet<Node> visited, ref int currentNumber)
    {
      Contract.Requires(n != null);
      if (visited.Contains(n))
      {
        return;
      }

      visited.Add(n);
      foreach (Node /*!*/ child in this.graph.Successors(n))
      {
        Contract.Assert(child != null);
        PostOrderVisit(child, visited, ref currentNumber);
      }

      Contract.Assume(this.postOrderNumberToNode != null);
      Contract.Assume(this.nodeToPostOrderNumber != null);
      this.postOrderNumberToNode[currentNumber] = n;
      this.nodeToPostOrderNumber[n] = currentNumber;
      currentNumber++;
      return;
    }

    // Iterative version: mimics the above recursive procedure
    private void PostOrderVisitIterative(Node n)
    {
      Contract.Requires(n != null);
      var visited = new HashSet<Node>();
      var grey = new HashSet<Node>();
      var stack = new Stack<Node>();

      int currentNumber = 1;

      stack.Push(n);
      visited.Add(n);

      while (stack.Count != 0)
      {
        var curr = stack.Pop();

        if (grey.Contains(curr))
        {
          Contract.Assume(this.postOrderNumberToNode != null);
          Contract.Assume(this.nodeToPostOrderNumber != null);
          this.postOrderNumberToNode[currentNumber] = curr;
          this.nodeToPostOrderNumber[curr] = currentNumber;
          currentNumber++;
        }
        else
        {
          grey.Add(curr);
          stack.Push(curr);
          foreach (Node /*!*/ child in this.graph.Successors(curr))
          {
            Contract.Assert(child != null);
            if (!visited.Contains(child))
            {
              visited.Add(child);
              stack.Push(child);
            }
          }
        }
      }
    }

    public Node LeastCommonAncestor(Node n1, Node n2)
    {
      int num1 = nodeToPostOrderNumber[n1], num2 = nodeToPostOrderNumber[n2];
      int lca = intersect(num1, num2, this.doms);
      return postOrderNumberToNode[lca];
    }
  }

  public class Graph<Node>
  {
    private HashSet<Tuple<Node /*!*/, Node /*!*/>> edges;
    private HashSet<Node> nodes;
    private Node source;
    private bool reducible;
    private HashSet<Node> headers;
    private Dictionary<Node, HashSet<Node>> backEdgeNodes;
    private Dictionary<Tuple<Node /*!*/, Node /*!*/>, HashSet<Node>> naturalLoops;
    private HashSet<Node> splitCandidates;

    private DomRelation<Node> dominatorMap = null;
    private Dictionary<Node, HashSet<Node>> predCache = new Dictionary<Node, HashSet<Node>>();
    private Dictionary<Node, HashSet<Node>> succCache = new Dictionary<Node, HashSet<Node>>();
    private bool predComputed;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(edges == null || Contract.ForAll(edges, p => p.Item1 != null && p.Item2 != null));
      Contract.Invariant(naturalLoops == null ||
                         Contract.ForAll(naturalLoops.Keys, p => p.Item2 != null && p.Item1 != null));
    }

    private class PreHeader
    {
      Node /*!*/
        myHeader;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(myHeader != null);
      }

      internal PreHeader(Node /*!*/ h)
      {
        Contract.Requires(h != null);
        myHeader = h;
      }

      [Pure]
      public override string /*!*/ ToString()
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return "#" + myHeader.ToString();
      }
    }

    public Graph(HashSet<Tuple<Node /*!*/, Node /*!*/>> edges)
    {
      Contract.Requires(cce.NonNullElements(edges) && Contract.ForAll(edges, p => p.Item1 != null && p.Item2 != null));
      this.edges = edges;

      // original A#
      //ns = Set<Node>{ x : <x,y> in es } + Set<Node>{ y : <x,y> in es };

      // closest Spec#
      //ns = new Set<Node>{ Tuple<Node,Node> p in edges; p.Item1 } + new Set<Node>{ Tuple<Node,Node> p in edges; p.Item2 };

      // 
      HashSet<Node> temp = new HashSet<Node>();
      foreach (Tuple<Node /*!*/, Node /*!*/> p in edges)
      {
        Contract.Assert(p.Item1 != null);
        temp.Add(p.Item1);
        Contract.Assert(p.Item2 != null);
        temp.Add(p.Item2);
      }

      nodes = temp;
    }

    public Graph()
    {
      edges = new HashSet<Tuple<Node /*!*/, Node /*!*/>>();
      nodes = new HashSet<Node>();
    }

    // BUGBUG: Set<T>.ToString() should return a non-null string
    [Pure]
    public override string /*!*/ ToString()
    {
      return "" + edges.ToString();
    }

    public void AddSource(Node /*!*/ x)
    {
      Contract.Requires(x != null);
      // BUGBUG: This generates bad code in the compiler
      //ns += new Set<Node>{x};
      nodes.Add(x);
      source = x;
    }

    public void AddEdge(Node /*!*/ source, Node /*!*/ dest)
    {
      Contract.Requires(source != null);
      Contract.Requires(dest != null);
      //es += Set<Edge>{<source,dest>};
      //ns += Set<Node>{source, dest};
      edges.Add(new Tuple<Node /*!*/, Node /*!*/>(source, dest));
      nodes.Add(source);
      nodes.Add(dest);
      predComputed = false;
    }

    public HashSet<Node> Nodes
    {
      get { return nodes; }
    }

    public IEnumerable<Tuple<Node /*!*/, Node /*!*/>> Edges
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Tuple<Node, Node>>>())
                         && Contract.ForAll(Contract.Result<IEnumerable<Tuple<Node, Node>>>(), n =>
                           n.Item1 != null && n.Item2 != null));
        return edges;
      }
    }

    public bool Edge(Node /*!*/ x, Node /*!*/ y)
    {
      Contract.Requires(x != null);
      Contract.Requires(y != null);
      // original A#
      // return <x,y> in es;
      return edges.Contains(new Tuple<Node /*!*/, Node /*!*/>(x, y));
    }

    private void ComputePredSuccCaches()
    {
      if (predComputed)
      {
        return;
      }

      predComputed = true;
      predCache = new Dictionary<Node, HashSet<Node>>();
      succCache = new Dictionary<Node, HashSet<Node>>();

      foreach (Node n in Nodes)
      {
        predCache[n] = new HashSet<Node>();
        succCache[n] = new HashSet<Node>();
      }

      foreach (Tuple<Node /*!*/, Node /*!*/> p in Edges)
      {
        Contract.Assert(p.Item1 != null);
        Contract.Assert(p.Item2 != null);
        HashSet<Node> tmp;

        tmp = predCache[p.Item2];
        tmp.Add(p.Item1);
        predCache[p.Item2] = tmp;

        tmp = succCache[p.Item1];
        tmp.Add(p.Item2);
        succCache[p.Item1] = tmp;
      }
    }

    public IEnumerable<Node> Predecessors(Node n)
    {
      // original A#
      //Set<Node> result = Set{ x : x in Nodes, Edge(x,n) };

      ComputePredSuccCaches();
      return predCache[n];
    }

    public IEnumerable<Node> Successors(Node n)
    {
      ComputePredSuccCaches();
      return succCache[n];
    }

    public List<Node> SuccessorsAsList(Node n)
    {
      ComputePredSuccCaches();
      List<Node> ret = new List<Node>();
      foreach (Node s in succCache[n])
      {
        ret.Add(s);
      }

      return ret;
    }

    public DomRelation<Node> /*Map<Node,Set<Node>>*/ DominatorMap
    {
      get
      {
        Contract.Assert(source != null);
        if (this.dominatorMap == null)
        {
          this.dominatorMap = new DomRelation<Node>(this, this.source);
        }

        return this.dominatorMap;
      }
    }

    // This method gives a simpler way to compute dominators but it assmumes the graph is a DAG.
    // With acyclicty we can compute all dominators by traversing the graph (once) in topological order
    // (using the property: A vertex's dominator set is unaffected by vertices that come later).
    // The method does not check the graph for the DAG property. That risk is on the caller.
    public Dictionary<Node, HashSet<Node>> DominatorsFast()
    {
      List<Node> topoSorted = this.TopologicalSort().ToList();
      var dominators = new Dictionary<Node, HashSet<Node>>();
      topoSorted.ForEach(u => dominators[u] = topoSorted.ToHashSet());
      var todo = new Queue<Node>();
      foreach (var u in topoSorted)
      {
        var s = new HashSet<Node>();
        var predecessors = this.Predecessors(u).ToList();
        if (predecessors.Count() != 0)
        {
          s.UnionWith(dominators[predecessors.First()]);
          predecessors.ForEach(v => s.IntersectWith(dominators[v]));
        }
        s.Add(u);
        dominators[u] = s;
      }
      return dominators;
    }

    // Use this method only for DAGs because it uses DominatorsFast() for computing dominators
    public Dictionary<Node, Node> ImmediateDominator()
    {
      List<Node> topoSorted = this.TopologicalSort().ToList();
      Dictionary<Node, HashSet<Node>> dominators = DominatorsFast();
      var immediateDominator = new Dictionary<Node, Node>();
      foreach (var u in this.Nodes)
      {
        if (dominators[u].Count() > 1)
        {
          dominators[u].Remove(u);
        }
        immediateDominator[u] = topoSorted.ElementAt(dominators[u].Max(e => topoSorted.IndexOf(e)));
      }
      immediateDominator[this.source] = this.source;
      return immediateDominator;
    }

    public Dictionary<Node, List<Node>> ImmediateDominatorMap
    {
      get
      {
        Contract.Assert(source != null);
        if (this.dominatorMap == null)
        {
          this.dominatorMap = new DomRelation<Node>(this, this.source);
        }

        return this.dominatorMap.ImmediateDominatorMap;
      }
    }

    public List<Node> ImmediatelyDominatedBy(Node /*!*/ n)
    {
      Contract.Requires(n != null);
      this.ImmediateDominatorMap.TryGetValue(n, out var dominees);
      return dominees == null ? new List<Node>() : dominees;
    }

    public IEnumerable<Node /*?*/> TopologicalSort(bool reversed = false)
    {
      this.TarjanTopSort(out var acyclic, out var sortedList, reversed);
      return acyclic ? sortedList : new List<Node>();
    }

    // From Tarjan 1972
    public void TarjanTopSort(out bool acyclic, out List<Node> sortedNodes, bool reversed = false)
    {
      int n = this.Nodes.Count;
      if (n == 0)
      {
        acyclic = true;
        sortedNodes = new List<Node>();
        return;
      }

      int[] incomingEdges = new int[n];
      // need an arbitrary numbering for the nodes to use as indices into
      // the arrays used within this algorithm
      Dictionary<Node, int> nodeToNumber = new Dictionary<Node, int>(n);
      Node[] numberToNode = new Node[n];
      int counter = 0;
      foreach (Node node in this.Nodes)
      {
        numberToNode[counter] = node;
        nodeToNumber[node] = counter;
        counter++;
      }

      foreach (Tuple<Node /*!*/, Node /*!*/> e in this.Edges)
      {
        Contract.Assert(e.Item1 != null);
        Contract.Assert(e.Item2 != null);
        Node /*!*/
          target = e.Item2;
        incomingEdges[nodeToNumber[target]]++;
      }

      List<Node> sorted = new List<Node>();
      int sortedIndex = 0;
      while (sortedIndex < n)
      {
        // find a root (i.e., its index)
        int rootIndex = -1;
        if (reversed)
        {
          for (int i = n - 1; i >= 0; i--)
          {
            if (incomingEdges[i] == 0)
            {
              rootIndex = i;
              break;
            }
          }
        }
        else
        {
          for (int i = 0; i < n; i++)
          {
            if (incomingEdges[i] == 0)
            {
              rootIndex = i;
              break;
            }
          }
        }

        if (rootIndex == -1)
        {
          acyclic = false;
          sortedNodes = new List<Node>();
          return;
        }

        // mark root so it won't be used again
        incomingEdges[rootIndex] = -1;
        Node root = numberToNode[rootIndex];
        sorted.Add(root);
        ++sortedIndex;
        foreach (Node s in this.Successors(root))
        {
          incomingEdges[nodeToNumber[s]]--;
        }
      }

      acyclic = true;
      sortedNodes = sorted;
      return;
    }

    private IEnumerable<Node> OldTopologicalSort()
    {
      Tuple<bool, List<Node>> result = this.TopSort();
      return result.Item1 ? result.Item2 : (IEnumerable<Node>) new List<Node>();
    }

    // From AsmL distribution example
    private Tuple<bool, List<Node>> TopSort()
    {
      List<Node> S = new List<Node>();
      HashSet<Node> V = this.Nodes;
      HashSet<Node> X = new HashSet<Node>();
      foreach (Node /*!*/ n in V)
      {
        Contract.Assert(n != null);
        X.Add(n);
      }

      bool change = true;
      while (change)
        // invariant: X = V - S
      {
        change = false;
        if (X.Count > 0)
        {
          foreach (Node /*!*/ n in X)
          {
            Contract.Assert(n != null);
            // see if n has any incoming edges from any other node in X
            bool inDegreeZero = true;
            foreach (Node /*!*/ u in X)
            {
              Contract.Assert(u != null);
              if (this.Edge(u, n))
              {
                inDegreeZero = false;
                break; // no point looking further
              }
            }

            if (inDegreeZero)
            {
              S.Add(n);
              X.Remove(n);
              change = true;
              break; // might as well go back and start looking through X from the beginning
            }
          }

          // Then we made it all the way through X without finding a source node
          if (!change)
          {
            return new Tuple<bool, List<Node>>(false, new List<Node>());
          }
        }
      }

      return new Tuple<bool, List<Node>>(true, S);
    }

    public static bool Acyclic(Graph<Node> g)
    {
      g.TarjanTopSort(out var acyclic, out var _);
      return acyclic;
    }

    // [Dragon, Fig. 10.15, p. 604. Algorithm for constructing the natural loop.]
    static HashSet<Node> NaturalLoop(Graph<Node> g, Tuple<Node /*!*/, Node /*!*/> backEdge)
    {
      Contract.Requires(backEdge.Item1 != null && backEdge.Item2 != null);
      Node /*!*/
        n = backEdge.Item1;
      Node /*!*/
        d = backEdge.Item2;
      Stack<Node> stack = new Stack<Node>();
      HashSet<Node> loop = new HashSet<Node>();
      loop.Add(d);
      if (!n.Equals(d)) // then n is not in loop
      {
        loop.Add(n);
        stack.Push(n); // push n onto stack
      }

      while (stack.Count > 0) // not empty
      {
        Node m = stack.Peek();
        stack.Pop(); // pop stack
        foreach (Node /*!*/ p in g.Predecessors(m))
        {
          Contract.Assert(p != null);
          if (!(loop.Contains(p)))
          {
            loop.Add(p);
            stack.Push(p); // push p onto stack
          }
        }
      }

      return loop;
    }

    internal struct ReducibleResult
    {
      internal bool reducible;
      internal HashSet<Node> headers;
      internal Dictionary<Node, HashSet<Node>> backEdgeNodes;
      internal Dictionary<Tuple<Node /*!*/, Node /*!*/>, HashSet<Node>> naturalLoops;
      internal HashSet<Node> splitCandidates;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Contract.ForAll(naturalLoops.Keys, p => p.Item1 != null && p.Item2 != null));
      }

      internal ReducibleResult(bool b, HashSet<Node> headers, Dictionary<Node, HashSet<Node>> backEdgeNodes,
        Dictionary<Tuple<Node /*!*/, Node /*!*/>, HashSet<Node>> naturalLoops, HashSet<Node> splitCandidates)
      {
        Contract.Requires(naturalLoops == null ||
                          Contract.ForAll(naturalLoops.Keys, Key => Key.Item1 != null && Key.Item2 != null));
        this.reducible = b;
        this.headers = headers;
        this.backEdgeNodes = backEdgeNodes;
        this.naturalLoops = naturalLoops;
        this.splitCandidates = splitCandidates;
      }
    }

    // [Dragon, p. 606]
    static ReducibleResult ComputeReducible(Graph<Node> g, Node source)
    {
      // first, compute the dom relation
      DomRelation<Node> /*Map<Node,Set<Node>>*/
        D = g.DominatorMap;
      return ComputeReducible(g, source, D);
    }

    static HashSet<Node> FindCycle(Graph<Node> g, Node source)
    {
      Stack<Tuple<Node, List<Node>>> stack = new Stack<Tuple<Node, List<Node>>>();
      HashSet<Node> stackAsSet = new HashSet<Node>();
      HashSet<Node> visited = new HashSet<Node>();
      stack.Push(new Tuple<Node, List<Node>>(source, g.SuccessorsAsList(source)));
      stackAsSet.Add(source);
      while (stack.Count > 0)
      {
        Tuple<Node, List<Node>> tuple = stack.Peek();
        List<Node> children = tuple.Item2;
        if (children.Count == 0)
        {
          stack.Pop();
          stackAsSet.Remove(tuple.Item1);
          continue;
        }

        Node n = children[0];
        children.RemoveAt(0);
        if (stackAsSet.Contains(n))
        {
          HashSet<Node> ret = new HashSet<Node>();
          ret.Add(n);
          while (true)
          {
            Node x = stack.Pop().Item1;
            if (x.Equals(n))
            {
              return ret;
            }
          }
        }

        if (visited.Contains(n))
        {
          continue;
        }

        stack.Push(new Tuple<Node, List<Node>>(n, g.SuccessorsAsList(n)));
        visited.Add(n);
        stackAsSet.Add(n);
        System.Diagnostics.Debug.Assert(stack.Count == stackAsSet.Count);
      }

      return new HashSet<Node>();
    }

    // [Dragon, p. 606]
    static ReducibleResult ComputeReducible(Graph<Node> g,
      Node source,
      DomRelation<Node> /*!*/ DomRelation)
    {
      Contract.Requires(DomRelation != null);

      //Console.WriteLine("[" + DateTime.Now +"]: begin ComputeReducible");
      IEnumerable<Tuple<Node /*!*/, Node /*!*/>> edges = g.Edges;
      Contract.Assert(Contract.ForAll(edges, n => n.Item1 != null && n.Item2 != null));
      HashSet<Tuple<Node /*!*/, Node /*!*/>> backEdges = new HashSet<Tuple<Node /*!*/, Node /*!*/>>();
      HashSet<Tuple<Node /*!*/, Node /*!*/>> nonBackEdges = new HashSet<Tuple<Node /*!*/, Node /*!*/>>();
      foreach (Tuple<Node /*!*/, Node /*!*/> e in edges)
      {
        Contract.Assert(e.Item1 != null);
        Contract.Assert(e.Item2 != null);
        Node x = e.Item1;
        Node y = e.Item2; // so there is an edge from x to y
        if (DomRelation.DominatedBy(x, y))
        {
          // y dom x: which means y dominates x
          backEdges.Add(e);
        }
        else
        {
          nonBackEdges.Add(e);
        }
      }

      Graph<Node> withoutBackEdges = new Graph<Node>(nonBackEdges);
      if (!Acyclic(withoutBackEdges))
      {
        return new ReducibleResult(false,
          new HashSet<Node>(),
          new Dictionary<Node, HashSet<Node>>(),
          new Dictionary<Tuple<Node /*!*/, Node /*!*/>, HashSet<Node>>(),
          FindCycle(withoutBackEdges, source));
      }
      else
      {
        // original A#:
        //Set<Node> headers = Set{ d : <n,d> in backEdges };
        HashSet<Node> headers = new HashSet<Node>();
        foreach (Tuple<Node /*!*/, Node /*!*/> e in backEdges)
        {
          Contract.Assert(e.Item1 != null);
          Contract.Assert(e.Item2 != null);
          headers.Add(e.Item2);
        }

        // original A#:
        //Map<Node,Set<Node>> backEdgeNodes = Map{ h -> bs  : h in headers, bs = Set<Node>{ b : <b,x> in backEdges, x == h } };
        Dictionary<Node, HashSet<Node>> backEdgeNodes = new Dictionary<Node, HashSet<Node>>();
        foreach (Node /*!*/ h in headers)
        {
          Contract.Assert(h != null);
          HashSet<Node> bs = new HashSet<Node>();
          foreach (Tuple<Node, Node> backedge in backEdges)
          {
            Contract.Assert(backedge.Item1 != null);
            Contract.Assert(backedge.Item2 != null);
            if (backedge.Item2.Equals(h))
            {
              bs.Add(backedge.Item1);
            }
          }

          backEdgeNodes.Add(h, bs);
        }

        // original A#:
        //Map<Tuple<Node,Node>,Set<Node>> naturalLoops = Map{ e -> NaturalLoop(g,e) : e in backEdges };
        Dictionary<Tuple<Node /*!*/, Node /*!*/>, HashSet<Node>> naturalLoops =
          new Dictionary<Tuple<Node /*!*/, Node /*!*/>, HashSet<Node>>();
        foreach (Tuple<Node /*!*/, Node /*!*/> e in backEdges)
        {
          Contract.Assert(e.Item1 != null && e.Item2 != null);
          naturalLoops.Add(e, NaturalLoop(g, e));
        }

        //Console.WriteLine("[" + DateTime.Now +"]: end ComputeReducible");
        return new ReducibleResult(true, headers, backEdgeNodes, naturalLoops, new HashSet<Node>());
      }
    }

    public bool Reducible
    {
      get { return reducible; }
    }

    public IEnumerable<Node> Headers
    {
      get { return headers; }
    }

    public IEnumerable<Node> BackEdgeNodes(Node /*!*/ h)
    {
      Contract.Requires(h != null);
      // original A#:
      //return h in backEdgeNodes ? backEdgeNodes[h] : null;
      return (backEdgeNodes.ContainsKey(h) ? backEdgeNodes[h] : (IEnumerable<Node>) new List<Node>());
    }

    public IEnumerable<Node> NaturalLoops(Node /*!*/ header, Node /*!*/ backEdgeNode)
    {
      Contract.Requires(header != null);
      Contract.Requires(backEdgeNode != null);
      Tuple<Node /*!*/, Node /*!*/> e = new Tuple<Node /*!*/, Node /*!*/>(backEdgeNode, header);
      return naturalLoops.ContainsKey(e) ? naturalLoops[e] : (IEnumerable<Node>) new List<Node>();
    }

    public HashSet<Node> SplitCandidates
    {
      get { return splitCandidates; }
    }

    public void ComputeLoops()
    {
      ReducibleResult r = ComputeReducible(this, this.source);
      this.reducible = r.reducible;
      this.headers = r.headers;
      this.backEdgeNodes = r.backEdgeNodes;
      this.naturalLoops = r.naturalLoops;
      this.splitCandidates = r.splitCandidates;
      return;
    }

    public IEnumerable<Node> SortHeadersByDominance()
    {
      Graph<Node> dag = new Graph<Node>();
      foreach (Node b in headers)
      {
        dag.AddSource(b);
        foreach (Node c in headers)
        {
          if (b.Equals(c))
          {
            continue;
          }

          if (DominatorMap.DominatedBy(b, c))
          {
            System.Diagnostics.Debug.Assert(!DominatorMap.DominatedBy(c, b));
            dag.AddEdge(b, c);
          }
        }
      }

      return dag.TopologicalSort();
    }

    public string ToDot(Func<Node, string> NodeLabel = null, Func<Node, string> NodeStyle = null)
    {
      NodeLabel = NodeLabel ?? (n => n.ToString());
      NodeStyle = NodeStyle ?? (n => "[shape=box]");
      var s = new StringBuilder();
      s.AppendLine("digraph G {");
      foreach (var n in Nodes)
      {
        s.AppendLine("  \"" + NodeLabel(n) + "\" " + NodeStyle(n) + ";");
      }

      foreach (var e in Edges)
      {
        s.AppendLine("  \"" + NodeLabel(e.Item1) + "\" -> \"" + NodeLabel(e.Item2) + "\";");
      }

      s.AppendLine("}");
      return s.ToString();
    }

    public ICollection<Node> ComputeReachability(Node start, bool forward = true)
    {
      var todo = new Stack<Node>();
      var visited = new HashSet<Node>();
      todo.Push(start);
      while (todo.Any())
      {
        var current = todo.Pop();
        if (!visited.Add(current))
        {
          continue;
        }

        var targets = forward ? this.Successors(current) : this.Predecessors(current);
        foreach (var target in targets) {
          if (!visited.Contains(target)) {
            todo.Push(target);
          }
        }
      }
      return visited;
    }

    public ICollection<Node> Reachable()
    {
      return ComputeReachability(source);
    }
  } // end: class Graph

  public static class GraphAlgorithms
  {
    /**
     * A merge node is a node that has multiple incoming edges, and which cannot be traversed unless all incoming edges have been traversed.
     * A merge node is represented by an object of type IEnumerable{object}
     */
    public static IEnumerable<object> FindReachableNodesInGraphWithMergeNodes(
      Dictionary<object, List<object>> edges, IEnumerable<object> roots, Func<object, object, bool> visitChild = null)
    {
      var todo = new Stack<object>(roots);
      var visitedEdges = new HashSet<object>();
      while (todo.Any())
      {
        var node = todo.Pop();
        if (visitedEdges.Contains(node)) {
          continue;
        }

        IReadOnlyList<object> parents; 
        if (node is IEnumerable<object> objects) {
          parents = objects.ToList();
          if (!visitedEdges.IsSupersetOf(parents)) {
            continue;
          }
        } else {
          parents = new[] { node };
        }
        visitedEdges.Add(node);

        var outgoing = edges.GetValueOrDefault(node) ?? new List<object>();
        foreach (var child in outgoing)
        {
          if (visitChild != null && parents.Any(p => !visitChild(p, child)))
          {
            continue;
          }
          todo.Push(child);
        }
      }
      return visitedEdges;
    }
    
    public static Graph<Node> Dual<Node>(this Graph<Node> g, Node dummySource)
    {
      var exits = g.Nodes.Where(n => g.Successors(n).Count() == 0).ToList();
      Node source;
      if (exits.Count == 0)
      {
        exits.Add(dummySource);
      }

      var dual = new Graph<Node>(
        new HashSet<Tuple<Node, Node>>(g.Edges.Select(e => new Tuple<Node, Node>(e.Item2, e.Item1))));
      if (exits.Count == 1)
      {
        dual.AddSource(exits[0]);
        source = exits[0];
      }
      else
      {
        dual.AddSource(dummySource);
        source = dummySource;
        foreach (var exit in exits)
        {
          dual.AddEdge(dummySource, exit);
        }
      }

      #region Dual graph may not be connected, so add an edge from the dual graph's soure node to any unreachable node

      foreach (var n in dual.Nodes.Where(Item => !dual.Reachable().Contains(Item)))
      {
        dual.AddEdge(source, n);
      }

      #endregion

      return dual;
    }

    public static List<Tuple<Node, bool>> LoopyTopSort<Node>(this Graph<Node> g)
    {
      Contract.Assert(g.Reducible);

      int n = g.Nodes.Count;
      var nodeToNumber = new Dictionary<Node, int>(n);
      var numberToNode = new Node[n];
      var allNodes = new List<int>();
      int counter = 0;
      foreach (Node node in g.Nodes)
      {
        numberToNode[counter] = node;
        nodeToNumber[node] = counter;
        allNodes.Add(counter);
        counter++;
      }

      var loops = new List<int>[n];
      foreach (var h in g.Headers)
      {
        var loopNodes = new HashSet<Node>();
        foreach (var b in g.BackEdgeNodes(h))
        {
          loopNodes.UnionWith(g.NaturalLoops(h, b));
        }

        loops[nodeToNumber[h]] =
          new List<int>(loopNodes.Select(node => nodeToNumber[node]));
      }

      var successors = new List<int>[n];
      var predecessors = new List<int>[n];
      int[] incomingEdges = new int[n];

      for (int i = 0; i < n; i++)
      {
        predecessors[i] = new List<int>();
      }

      foreach (var e in g.Edges)
      {
        Contract.Assert(e.Item1 != null);
        Contract.Assert(e.Item2 != null);
        int source = nodeToNumber[e.Item1], target = nodeToNumber[e.Item2];
        if (loops[target] == null || !loops[target].Contains(source))
        {
          if (successors[source] == null)
          {
            successors[source] = new List<int>();
          }

          successors[source].Add(target);
          incomingEdges[target]++;
        }

        predecessors[target].Add(source);
      }

      var sortedNodes = new List<Tuple<Node, bool>>();
      var sortedNodesInternal = new List<int>();

      var regionStack = new Stack<Tuple<Node, List<int>>>();
      regionStack.Push(new Tuple<Node, List<int>>(default(Node), allNodes));

      while (regionStack.Count != 0)
      {
        var rootIndexes = new List<int>();
        foreach (var i in regionStack.Peek().Item2)
        {
          if (incomingEdges[i] == 0)
          {
            rootIndexes.Add(i);
          }
        }

        if (rootIndexes.Count() == 0)
        {
          var region = regionStack.Pop();
          if (regionStack.Count != 0)
          {
            sortedNodes.Add(new Tuple<Node, bool>(region.Item1, true));
            sortedNodesInternal.Add(nodeToNumber[region.Item1]);
          }

          continue;
        }

        int rootIndex = rootIndexes[0];
        int maxPredIndex = -1;
        foreach (var i in rootIndexes)
        {
          foreach (var p in predecessors[i])
          {
            int predIndex =
              sortedNodesInternal.FindLastIndex(x => x == p);
            if (predIndex > maxPredIndex)
            {
              rootIndex = i;
              maxPredIndex = predIndex;
            }
          }
        }

        incomingEdges[rootIndex] = -1;
        sortedNodes.Add(new Tuple<Node, bool>(numberToNode[rootIndex], false));
        sortedNodesInternal.Add(rootIndex);
        if (successors[rootIndex] != null)
        {
          foreach (int s in successors[rootIndex])
          {
            incomingEdges[s]--;
          }
        }

        if (loops[rootIndex] != null)
        {
          regionStack.Push(new Tuple<Node, List<int>>(numberToNode[rootIndex],
            loops[rootIndex]));
        }
      }

      return sortedNodes;
    }

    // Algorithm from Jeanne Ferrante, Karl J. Ottenstein, Joe D. Warren,
    // "The Program Dependence Graph and Its Use in Optimization"
    public static Dictionary<Node, HashSet<Node>> ControlDependence<Node>(this Graph<Node> g) where Node : class, new()
    {
      Graph<Node> dual = g.Dual(new Node());
      DomRelation<Node> pdom = dual.DominatorMap;

      var result = new Dictionary<Node, HashSet<Node>>();

      var S = g.Edges.Where(e => !pdom.DominatedBy(e.Item1, e.Item2));
      foreach (var edge in S)
      {
        var L = pdom.LeastCommonAncestor(edge.Item1, edge.Item2);
        var deps = new List<Node>();
        if (L == edge.Item1)
        {
          pdom.DominatedBy(edge.Item2, edge.Item1, deps);
          deps.Add(edge.Item2);
          deps.Add(edge.Item1);
        }
        else
        {
          pdom.DominatedBy(edge.Item2, L, deps);
          deps.Add(edge.Item2);
        }

        if (result.ContainsKey(edge.Item1))
        {
          result[edge.Item1].UnionWith(deps);
        }
        else
        {
          result[edge.Item1] = new HashSet<Node>(deps);
        }
      }

      return result;
    }

    public static void TransitiveClosure<Node>(this Dictionary<Node, HashSet<Node>> graph) where Node : class
    {
      bool changed;
      do
      {
        changed = false;
        foreach (var entry in graph)
        {
          var newSuccessors = new HashSet<Node>(entry.Value);
          foreach (var successor in entry.Value)
          {
            if (graph.ContainsKey(successor))
            {
              newSuccessors.UnionWith(graph[successor]);
            }
          }

          if (newSuccessors.Count != entry.Value.Count)
          {
            entry.Value.UnionWith(newSuccessors);
            changed = true;
          }
        }
      } while (changed);
    }
  }

  public delegate System.Collections.IEnumerable /*<Node!>*/ /*!*/ Adjacency<T>(T /*!*/ node);


  // An SCC is a set of nodes
  public sealed class SCC<Node> : ICollection<Node>
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(nodesMap != null);
    }

    private IDictionary<Node, object> /*!*/
      nodesMap = new Dictionary<Node, object>();

    private ICollection<Node> /*!*/ nodes
    {
      get { return cce.NonNull(nodesMap.Keys); }
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    System.Collections.IEnumerator /*!*/ System.Collections.IEnumerable.GetEnumerator()
    {
      Contract.Ensures(Contract.Result<System.Collections.IEnumerator>() != null);

      return ((System.Collections.IEnumerable) nodes).GetEnumerator();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator<Node> /*!*/ IEnumerable<Node>.GetEnumerator()
    {
      Contract.Ensures(Contract.Result<IEnumerator<Node>>() != null);

      return ((IEnumerable<Node>) nodes).GetEnumerator();
    }

    public int Count
    {
      get { return nodes.Count; }
    }

    public bool IsReadOnly
    {
      get { return nodesMap.IsReadOnly; }
    }

    public void Add(Node item)
    {
      nodesMap.Add(item, null);
    }

    public void Clear()
    {
      nodesMap.Clear();
    }

    [Pure]
    public bool Contains(Node item)
    {
      return nodesMap.ContainsKey(item);
    }

    public void CopyTo(Node[] array, int arrayIndex)
    {
      //Contract.Requires(array != null);
      nodes.CopyTo(array, arrayIndex);
    }

    public bool Remove(Node item)
    {
      return nodesMap.Remove(item);
    }
  }

  public sealed class StronglyConnectedComponents<Node> : IEnumerable<SCC<Node> /*!*/> where Node : class
  {
    private readonly IDictionary<Node /*!*/, object> /*!*/
      graph;

    [ContractInvariantMethod]
    void graphInvariantMethod()
    {
      Contract.Invariant(Contract.ForAll(graph, entry => entry.Key != null));
      Contract.Invariant(preds != null);
      Contract.Invariant(succs != null);
    }

    private readonly Adjacency<Node> /*!*/
      preds;

    private readonly Adjacency<Node> /*!*/
      succs;

    private bool computed = false;

    public bool Computed
    {
      get { return computed; }
    }

    [NotDelayed]
    public StronglyConnectedComponents(System.Collections.IEnumerable /*<Node!>*/ graph, Adjacency<Node> preds,
      Adjacency<Node> succs)
      : base()
    {
      Contract.Requires(succs != null);
      Contract.Requires(preds != null);
      Contract.Requires(graph != null);
      Contract.Ensures(!Computed);
      IDictionary<Node /*!*/, object> /*!*/
        dict = new Dictionary<Node /*!*/, object>();
      foreach (Node /*!*/ n in graph)
      {
        Contract.Assert(n != null);
        dict.Add(n, null);
      }

      this.graph = dict;
      this.preds = preds;
      this.succs = succs;
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    System.Collections.IEnumerator /*!*/ System.Collections.IEnumerable.GetEnumerator()
    {
      Contract.Ensures(Contract.Result<System.Collections.IEnumerator>() != null);

      return ((System.Collections.IEnumerable) sccs).GetEnumerator();
    }

    [Pure]
    [GlobalAccess(false)]
    [Escapes(true, false)]
    IEnumerator<SCC<Node> /*!*/> /*!*/ IEnumerable<SCC<Node> /*!*/>.GetEnumerator()
    {
      Contract.Ensures(Contract.Result<IEnumerator<SCC<Node>>>() != null);

      Contract.Assume(Computed);
      Contract.Assert(cce.NonNullElements((IEnumerable<SCC<Node> /*!*/>) sccs)); //REVIEW
      return ((IEnumerable<SCC<Node> /*!*/>) sccs).GetEnumerator();
    }

    private readonly IList<SCC<Node> /*!*/> /*!*/
      sccs = new List<SCC<Node> /*!*/>();

    [ContractInvariantMethod]
    void sccsInvariant()
    {
      Contract.Invariant(cce.NonNullElements(sccs));
    }


    public void Compute()
    {
      Contract.Requires(!Computed);
      Contract.Ensures(Computed);
      // Compute post times on graph with edges reversed
      this.dfsNext = this.preds;
      foreach (Node /*!*/ n in cce.NonNull(graph.Keys))
      {
        Contract.Assert(n != null);
        if (!seen.ContainsKey(n))
        {
          OrderNodes(n);
        }
      }

      // Clear seen
      seen.Clear();

      // Compute SCCs
      this.dfsNext = this.succs;
      while (postOrder.Count > 0)
      {
        Node /*!*/
          n = postOrder.Pop();
        Contract.Assert(n != null);

        if (!seen.ContainsKey(n))
        {
          SCC<Node> /*!*/
            curr = new SCC<Node>();
          FindSCCs(n, curr);
          sccs.Add(curr);
        }
      }

      // Clear seen
      seen.Clear();

      this.computed = true;
    }

    private Adjacency<Node> /*?*/
      dfsNext = null;

    private readonly IDictionary<Node /*!*/, object> /*!*/
      seen = new Dictionary<Node /*!*/, object>();

    private readonly Stack<Node /*!*/> /*!*/
      postOrder = new Stack<Node /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(seen != null);
      Contract.Invariant(cce.NonNullElements(postOrder));
    }


    // DFS to order nodes by post times
    private void OrderNodes(Node node)
    {
      Contract.Requires(node != null);
      seen.Add(node, null);

      Contract.Assert(dfsNext != null);
      System.Collections.IEnumerable /*!*/
        nexts = dfsNext(node);
      Contract.Assert(nexts != null);
      foreach (Node /*!*/ n in nexts)
      {
        Contract.Assert(n != null);
        if (graph.ContainsKey(n) && !seen.ContainsKey(n))
        {
          OrderNodes(n);
        }
      }

      postOrder.Push(node);
    }

    // DFS to compute SCCs
    private void FindSCCs(Node node, SCC<Node> currSCC)
    {
      Contract.Requires(currSCC != null);
      Contract.Requires(node != null);
      //modifies currSCC.*;
      seen.Add(node, null);
      currSCC.Add(node);

      Contract.Assert(dfsNext != null);
      System.Collections.IEnumerable /*!*/
        nexts = dfsNext(node);
      Contract.Assert(nexts != null);
      foreach (Node /*!*/ n in nexts)
      {
        Contract.Assert(n != null);
        if (graph.ContainsKey(n) && !seen.ContainsKey(n))
        {
          FindSCCs(n, currSCC);
        }
      }
    }

    [Pure]
    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      string outStr = "";
      int i = 0;

      foreach (ICollection<Node> component in this)
      {
        string /*!*/
          tmp = System.String.Format("\nComponent #{0} = ", i++);
        Contract.Assert(tmp != null);
        outStr += tmp;

        bool firstInRow = true;

        foreach (Node b in component)
        {
          string /*!*/
            tmpComponent = System.String.Format("{0}{1}", firstInRow ? "" : ", ", b);
          Contract.Assert(tmpComponent != null);
          outStr += tmpComponent;
          firstInRow = false;
        }
      }

      return outStr;
    }
  }

  public class GraphProgram
  {
    static void TestGraph<T>(T /*!*/ source, params Tuple<T /*!*/, T /*!*/>[] edges)
    {
      Contract.Requires(source != null);
      Contract.Requires(Contract.ForAll(edges, pair => pair.Item1 != null && pair.Item2 != null));
      HashSet<Tuple<T /*!*/, T /*!*/>> es = new HashSet<Tuple<T /*!*/, T /*!*/>>();
      foreach (Tuple<T /*!*/, T /*!*/> e in edges)
      {
        Contract.Assert(e.Item1 != null && e.Item2 != null);
        es.Add(e);
      }

      Graph<T> g = new Graph<T>(es);
      g.AddSource(source);
      Console.WriteLine("G = " + g);
      g.ComputeLoops();
      Console.WriteLine("G's Dominator Map = " + g.DominatorMap);
      Console.WriteLine("G's Immediate Dominator Map = " + Util.MapToString(g.ImmediateDominatorMap));
      Console.WriteLine("G is reducible: " + (g.Reducible ? "yes" : "no"));
    }

    static void Main(string[] args)
      //requires forall{string s in args; s != null};
    {
      Console.WriteLine("Spec# says hello!");
      // This generates bad IL -- need to fix a bug in the compiler
      //Graph<int> g = new Graph<int>(new Set<Tuple<int,int>>{ new Tuple<int,int>(1,2), new Tuple<int,int>(1,3), new Tuple<int,int>(2,3) });

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'c')
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'd'),
        new Tuple<char, char>('c', 'e'),
        new Tuple<char, char>('c', 'f'),
        new Tuple<char, char>('d', 'e'),
        new Tuple<char, char>('e', 'd'),
        new Tuple<char, char>('e', 'f'),
        new Tuple<char, char>('f', 'e')
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'c'),
        new Tuple<char, char>('c', 'b')
      );

      Console.WriteLine("");
      TestGraph<int>(1,
        new Tuple<int, int>(1, 2),
        new Tuple<int, int>(1, 3),
        new Tuple<int, int>(2, 3)
      );

      Console.WriteLine("");
      TestGraph<int>(1,
        new Tuple<int, int>(1, 2),
        new Tuple<int, int>(1, 3),
        new Tuple<int, int>(2, 3),
        new Tuple<int, int>(3, 2)
      );

      Console.WriteLine("");
      TestGraph<int>(2,
        new Tuple<int, int>(2, 3),
        new Tuple<int, int>(2, 4),
        new Tuple<int, int>(3, 2)
      );

      Console.WriteLine("");
      TestGraph<char>('a',
        new Tuple<char, char>('a', 'b'),
        new Tuple<char, char>('a', 'c'),
        new Tuple<char, char>('b', 'c'),
        new Tuple<char, char>('b', 'b')
      );
    }
  }
}