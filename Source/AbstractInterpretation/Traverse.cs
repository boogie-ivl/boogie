using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  /// <summary>
  /// This class provides the functionality of traversing a program to determine which
  /// blocks are blocks where the widening operator may need to be applied.  Assumes
  /// all 'currentlyTraversed' bits to be initially false, and leaves them that way in
  /// the end.  Assumes the 'widenBlock' bits are initially false, and sets them
  /// appropriately.
  /// </summary>
  public class WidenPoints
  {
    /// <summary>
    /// Compute the widen points of a program
    /// </summary>
    public static void Compute(Program program)
    {
      Contract.Requires(program != null);
      Cce.BeginExpose(program);

      foreach (var impl in program.Implementations)
      {
        if (impl.Blocks != null && impl.Blocks.Count > 0)
        {
          Contract.Assume(Cce.IsConsistent(impl));
          Cce.BeginExpose(impl);
          Block start = impl.Blocks[0];
          Contract.Assume(start != null);
          Contract.Assume(Cce.IsConsistent(start));
          Visit(start);

          // We reset the state...
          foreach (Block b in impl.Blocks)
          {
            Cce.BeginExpose(b);
            b.TraversingStatus = Block.VisitState.ToVisit;
            Cce.EndExpose();
          }

          Cce.EndExpose();
        }
      }

      Cce.EndExpose();
    }

    static void Visit(Block b)
    {
      Contract.Requires(b != null);
      Contract.Assume(Cce.IsExposable(b));
      if (b.TraversingStatus == Block.VisitState.BeingVisited)
      {
        Cce.BeginExpose(b);
        // we got here through a back-edge
        b.widenBlock = true;
        Cce.EndExpose();
      }
      else if (b.TraversingStatus == Block.VisitState.AlreadyVisited)
      {
        // do nothing... we already saw this node
      }
      else if (b.TransferCmd is GotoCmd)
      {
        Contract.Assert(b.TraversingStatus == Block.VisitState.ToVisit);

        GotoCmd g = (GotoCmd) b.TransferCmd;
        Cce.BeginExpose(b);

        Cce.BeginExpose(g); //PM: required for the subsequent expose (g.labelTargets)
        b.TraversingStatus = Block.VisitState.BeingVisited;

        // labelTargets is made non-null by Resolve, which we assume
        // has already called in a prior pass.
        Contract.Assume(g.labelTargets != null);
        Cce.BeginExpose(g.labelTargets);
        foreach (Block succ in g.labelTargets)
          //              invariant b.currentlyTraversed;
          //PM: The following loop invariant will work once properties are axiomatized
          //&& (g.labelNames != null && g.labelTargets != null ==> g.labelNames.Length == g.labelTargets.Length);
        {
          Contract.Assert(succ != null);
          Visit(succ);
        }

        Cce.EndExpose();

        Contract.Assert(b.TraversingStatus == Block.VisitState.BeingVisited);
        //            System.Diagnostics.Debug.Assert(b.currentlyTraversed);

        b.TraversingStatus = Block.VisitState.AlreadyVisited;

        //PM: The folowing assumption is needed because we cannot prove that a simple field update
        //PM: leaves the value of a property unchanged.
        Contract.Assume(g.labelNames == null || g.labelNames.Count == g.labelTargets.Count);
        Cce.EndExpose();
      }
      else
      {
        Contract.Assert(b.TransferCmd == null || b.TransferCmd is ReturnCmd); // It must be a returnCmd;
      }
    }

    static private Block rootBlock = null; // The root point we have to consider

    /// <summary>
    /// Compute the blocks in the body loop. 
    /// <param name ="block"> Tt is the head of the loop. It must be a widen block </param>
    /// <return> The blocks that are in the loop from block </return>
    /// </summary>
    public static List<Block> ComputeLoopBodyFrom(Block block)
    {
      Contract.Requires(block.widenBlock);
      Contract.Requires(block != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Block>>()));

      Contract.Assert(rootBlock == null);
      rootBlock = block;

      List<Block /*!*/> blocksInLoop = new List<Block /*!*/>(); // We use a list just because .net does not define a set
      List<Block /*!*/> visitingPath = new List<Block /*!*/>(); // The order is important, as we want paths

      blocksInLoop.Add(block);

      DoDFSVisit(block, visitingPath, blocksInLoop);

      visitingPath.Add(block);


      rootBlock = null; // We reset the invariant

      return blocksInLoop;
    }

    /// <summary>
    /// Perform the Depth-first search of the so to find the loop
    /// <param name = "block"> The block to visit </param>
    /// <param name = "path"> The path we are visiting so far </param>
    /// </summary>
    private static void DoDFSVisit(Block block, List<Block> path, List<Block> blocksInPath)
    {
      Contract.Requires(block != null);
      Contract.Requires(Cce.NonNullElements(path));
      Contract.Requires(Cce.NonNullElements(path));

      #region case 1. We visit the root => We are done, "path" is a path inside the loop

      if (block == rootBlock && path.Count > 1)
      {
        blocksInPath.AddRange(path); // Add all the blocks in this path 
      }

      #endregion

      #region case 2. We visit a node that ends with a return => "path" is not inside the loop

      if (block.TransferCmd is ReturnCmd)
      {
        return;
      }

      #endregion

      #region case 3. We visit a node with successors => continue the exploration of its successors

      {
        Contract.Assert(block.TransferCmd is GotoCmd);
        GotoCmd successors = (GotoCmd) block.TransferCmd;
        Contract.Assert(successors != null);

        if (successors.labelTargets != null)
        {
          foreach (Block nextBlock in successors.labelTargets)
          {
            Contract.Assert(nextBlock != null);
            if (path.Contains(nextBlock)) // If the current path has already seen the block, just skip it 
            {
              continue;
            }
            // Otherwise we perform the DFS visit
            path.Add(nextBlock);
            DoDFSVisit(nextBlock, path, blocksInPath);

            Contract.Assert(nextBlock == path[path.Count - 1]);
            path.RemoveAt(path.Count - 1);
          }
        }
      }

      #endregion
    }
  }
}