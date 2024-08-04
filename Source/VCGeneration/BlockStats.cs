using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace VC;

class BlockStats
{
  public bool bigBlock;
  public int id;
  public double assertionCost;
  public double assumptionCost; // before multiplier
  public double incomingPaths;

  public List<Block> /*!>!*/ virtualSuccessors = new List<Block>();

  public List<Block> /*!>!*/ virtualPredecessors = new List<Block>();

  public HashSet<Block> reachableBlocks;
  public readonly Block block;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullElements(virtualSuccessors));
    Contract.Invariant(Cce.NonNullElements(virtualPredecessors));
    Contract.Invariant(block != null);
  }


  public BlockStats(Block b, int i)
  {
    Contract.Requires(b != null);
    block = b;
    assertionCost = -1;
    id = i;
  }
}