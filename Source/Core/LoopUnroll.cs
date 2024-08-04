using System.Diagnostics.Contracts;
using System.Collections.Generic;
using Bpl = Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class LoopUnroll
  {
    public static List<Block /*!*/> /*!*/ UnrollLoops(Block start, int unrollMaxDepth, bool soundLoopUnrolling)
    {
      Contract.Requires(start != null);

      Contract.Requires(0 <= unrollMaxDepth);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Block>>()));
      Dictionary<Block, GraphNode /*!*/> gd = new Dictionary<Block, GraphNode /*!*/>();
      HashSet<Block> beingVisited = new HashSet<Block>();
      GraphNode gStart = GraphNode.ComputeGraphInfo(null, start, gd, beingVisited);

      // Compute SCCs
      StronglyConnectedComponents<GraphNode /*!*/> sccs =
        new StronglyConnectedComponents<GraphNode /*!*/>(gd.Values, Preds, Succs);
      Contract.Assert(sccs != null);
      sccs.Compute();
      Dictionary<GraphNode /*!*/, SCC<GraphNode /*!*/>> containingSCC =
        new Dictionary<GraphNode /*!*/, SCC<GraphNode /*!*/>>();
      foreach (SCC<GraphNode /*!*/> scc in sccs)
      {
        foreach (GraphNode /*!*/ n in scc)
        {
          Contract.Assert(n != null);
          containingSCC[n] = scc;
        }
      }

      LoopUnroll lu = new LoopUnroll(unrollMaxDepth, soundLoopUnrolling, containingSCC, new List<Block /*!*/>());
      lu.Visit(gStart);
      lu.newBlockSeqGlobal.Reverse();
      return lu.newBlockSeqGlobal;
    }

    // This is supposed to "undo" to effect of loop unrolling
    // on block labels. It essentially removes the "#num" from the end 
    // of lab, if there is something like this
    public static string sanitizeLabel(string lab)
    {
      if (!lab.Contains("#"))
      {
        return lab;
      }

      // Find the last occurrance of "#"
      int pos = lab.LastIndexOf('#');

      return lab.Substring(0, pos);
    }

    private static System.Collections.IEnumerable /*<GraphNode/*!>/*!*/ Succs(GraphNode n)
    {
      Contract.Requires(n != null);
      Contract.Ensures(Contract.Result<System.Collections.IEnumerable>() != null);

      List<GraphNode /*!*/> /*!*/
        AllEdges = new List<GraphNode /*!*/>();
      AllEdges.AddRange(n.ForwardEdges);
      AllEdges.AddRange(n.BackEdges);
      return AllEdges;
    }

    private static System.Collections.IEnumerable /*<GraphNode!>*/ /*!*/ Preds(GraphNode n)
    {
      Contract.Requires(n != null);
      Contract.Ensures(Contract.Result<System.Collections.IEnumerable>() != null);

      return n.Predecessors;
    }

    class GraphNode
    {
      public readonly Block /*!*/
        Block;

      public readonly List<Cmd> /*!*/
        Body;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Block != null);
        Contract.Invariant(Body != null);
        Contract.Invariant(Cce.NonNullElements(ForwardEdges));
        Contract.Invariant(Cce.NonNullElements(BackEdges));
        Contract.Invariant(Cce.NonNullElements(Predecessors));
        Contract.Invariant(isCutPoint == (BackEdges.Count != 0));
      }

      bool isCutPoint; // is set during ComputeGraphInfo

      public bool IsCutPoint
      {
        get { return isCutPoint; }
      }

      [Rep] public readonly List<GraphNode /*!*/> /*!*/ ForwardEdges = new List<GraphNode /*!*/>();
      [Rep] public readonly List<GraphNode /*!*/> /*!*/ BackEdges = new List<GraphNode /*!*/>();
      [Rep] public readonly List<GraphNode /*!*/> /*!*/ Predecessors = new List<GraphNode /*!*/>();

      GraphNode(Block b, List<Cmd> body)
      {
        Contract.Requires(body != null);
        Contract.Requires(b != null);
        this.Block = b;
        this.Body = body;
      }

      static List<Cmd> GetOptimizedBody(List<Cmd> cmds)
      {
        Contract.Requires(cmds != null);
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);
        int n = 0;
        foreach (Cmd c in cmds)
        {
          n++;
          PredicateCmd pc = c as PredicateCmd;
          if (pc != null && pc.Expr is LiteralExpr && ((LiteralExpr) pc.Expr).IsFalse)
          {
            // return a sequence consisting of the commands seen so far
            Cmd[] s = new Cmd[n];
            for (int i = 0; i < n; i++)
            {
              s[i] = cmds[i];
            }

            return new List<Cmd>(s);
          }
        }

        return cmds;
      }

      public static GraphNode ComputeGraphInfo(GraphNode from, Block b,
        Dictionary<Block /*!*/, GraphNode /*!*/> /*!*/ gd, HashSet<Block> beingVisited)
      {
        Contract.Requires(beingVisited != null);
        Contract.Requires(b != null);
        Contract.Requires(Cce.NonNullDictionaryAndValues(gd));
        Contract.Ensures(Contract.Result<GraphNode>() != null);
        if (gd.TryGetValue(b, out var g))
        {
          Contract.Assume(from != null);
          Contract.Assert(g != null);
          if (beingVisited.Contains(b))
          {
            // it's a cut point
            g.isCutPoint = true;
            from.BackEdges.Add(g);
            g.Predecessors.Add(from);
          }
          else
          {
            from.ForwardEdges.Add(g);
            g.Predecessors.Add(from);
          }
        }
        else
        {
          List<Cmd> body = GetOptimizedBody(b.Cmds);
          g = new GraphNode(b, body);
          gd.Add(b, g);
          if (from != null)
          {
            from.ForwardEdges.Add(g);
            g.Predecessors.Add(from);
          }

          if (body != b.Cmds)
          {
            // the body was optimized -- there is no way through this block
          }
          else
          {
            beingVisited.Add(b);

            GotoCmd gcmd = b.TransferCmd as GotoCmd;
            if (gcmd != null)
            {
              Contract.Assume(gcmd.labelTargets != null);
              foreach (Block /*!*/ succ in gcmd.labelTargets)
              {
                Contract.Assert(succ != null);
                ComputeGraphInfo(g, succ, gd, beingVisited);
              }
            }

            beingVisited.Remove(b);
          }
        }

        return g;
      }
    }

    readonly List<Block /*!*/> /*!*/
      newBlockSeqGlobal;

    readonly Dictionary<GraphNode /*!*/, SCC<GraphNode /*!*/>> /*!*/
      containingSCC;

    readonly int c;
    readonly bool soundLoopUnrolling;
    readonly LoopUnroll next;

    readonly LoopUnroll /*!*/
      head;

    Dictionary<Block, Block /*!*/> /*!*/
      newBlocks = new Dictionary<Block, Block /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(head != null);
      Contract.Invariant(Cce.NonNullElements(newBlockSeqGlobal));
      Contract.Invariant(newBlocks != null && Cce.NonNullElements(newBlocks.Values));
    }


    [NotDelayed]
    private LoopUnroll(int unrollMaxDepth, bool soundLoopUnrolling,
      Dictionary<GraphNode /*!*/, SCC<GraphNode /*!*/>> /*!*/ scc, List<Block /*!*/> /*!*/ newBlockSeqGlobal)
      : base()
    {
      Contract.Requires(Cce.NonNullElements(newBlockSeqGlobal));
      Contract.Requires(Cce.NonNullDictionaryAndValues(scc) &&
                        Contract.ForAll(scc.Values, v => Cce.NonNullElements(v)));
      Contract.Requires(0 <= unrollMaxDepth);
      this.newBlockSeqGlobal = newBlockSeqGlobal;
      this.c = unrollMaxDepth;
      this.containingSCC = scc;
      this.head = this;
      if (unrollMaxDepth != 0)
      {
        next = new LoopUnroll(unrollMaxDepth - 1, soundLoopUnrolling, scc, newBlockSeqGlobal, this);
      }
    }

    private LoopUnroll(int unrollMaxDepth, bool soundLoopUnrolling,
      Dictionary<GraphNode /*!*/, SCC<GraphNode /*!*/>> scc, List<Block /*!*/> /*!*/ newBlockSeqGlobal, LoopUnroll head)
    {
      Contract.Requires(head != null);
      Contract.Requires(Cce.NonNullDictionaryAndValues(scc));
      Contract.Requires(Cce.NonNullElements(newBlockSeqGlobal));
      Contract.Requires(0 <= unrollMaxDepth);
      this.newBlockSeqGlobal = newBlockSeqGlobal;
      this.c = unrollMaxDepth;
      this.soundLoopUnrolling = soundLoopUnrolling;
      this.containingSCC = scc;
      this.head = head;
      if (unrollMaxDepth != 0)
      {
        next = new LoopUnroll(unrollMaxDepth - 1, soundLoopUnrolling, scc, newBlockSeqGlobal, head);
      }
    }

    Block Visit(GraphNode node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Block>() != null);
      Block orig = node.Block;
      if (newBlocks.TryGetValue(orig, out var nw))
      {
        Contract.Assert(nw != null);
      }
      else
      {
        List<Cmd> body;
        TransferCmd tcmd;
        Contract.Assert(orig.TransferCmd != null);

        if (next == null && node.IsCutPoint)
        {
          // as the body, use the assert/assume commands that make up the loop invariant
          body = new List<Cmd>();
          foreach (Cmd /*!*/ c in node.Body)
          {
            Contract.Assert(c != null);
            if (c is PredicateCmd || c is CommentCmd)
            {
              body.Add(c);
            }
            else
            {
              break;
            }
          }

          if (soundLoopUnrolling)
          {
            body.Add(new AssertCmd(orig.tok, Bpl.Expr.False));
          }
          else
          {
            body.Add(new AssumeCmd(orig.tok, Bpl.Expr.False));
          }

          tcmd = new ReturnCmd(orig.TransferCmd.tok);
        }
        else
        {
          body = node.Body;
          List<Block> newSuccs = new List<Block>();

          foreach (GraphNode succ in node.ForwardEdges)
          {
            Block s;
            if (containingSCC[node] == containingSCC[succ])
            {
              s = Visit(succ);
            }
            else
            {
              Contract.Assert(head != null); // follows from object invariant
              s = head.Visit(succ);
            }

            newSuccs.Add(s);
          }

          Contract.Assert(next != null ||
                          node.BackEdges.Count == 0); // follows from if-else test above and the GraphNode invariant
          foreach (GraphNode succ in node.BackEdges)
          {
            Contract.Assert(next != null); // since if we get here, node.BackEdges.Count != 0
            Block s = next.Visit(succ);
            newSuccs.Add(s);
          }

          if (newSuccs.Count == 0)
          {
            tcmd = new ReturnCmd(orig.TransferCmd.tok);
          }
          else
          {
            tcmd = new GotoCmd(orig.TransferCmd.tok, newSuccs);
          }
        }

        nw = new Block(orig.tok, orig.Label + "#" + this.c, body, tcmd);
        newBlocks.Add(orig, nw);
        newBlockSeqGlobal.Add(nw);
      }

      return nw;
    }
  }
}