using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;

public static class ManualSplitFinder
{
  
  public static List<Split> FocusAndSplit(VCGenOptions options, ImplementationRun run, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerificationConditionGenerator par, bool splitOnEveryAssert)
  {
    List<Split> focussedImpl = FocusAttribute.FocusImpl(options, run, gotoCmdOrigins, par);
    var splits = focussedImpl.Select(s => FindManualSplits(s, splitOnEveryAssert)).SelectMany(x => x).ToList();
    return splits;
  }
  
  public static List<Split> FindManualSplits(Split initialSplit, bool splitOnEveryAssert)
  {
    Contract.Requires(initialSplit.Implementation != null);
    Contract.Ensures(Contract.Result<List<Split>>() == null || cce.NonNullElements(Contract.Result<List<Split>>()));

    var splitPoints = new Dictionary<Block, int>();
    foreach (var b in initialSplit.Blocks)
    {
      foreach (Cmd c in b.Cmds)
      {
        var p = c as PredicateCmd;
        if (ShouldSplitHere(c, splitOnEveryAssert))
        {
          splitPoints.TryGetValue(b, out var count);
          splitPoints[b] = count + 1;
        }
      }
    }
    var splits = new List<Split>();
    if (!splitPoints.Any())
    {
      splits.Add(initialSplit);
    }
    else
    {
      Block entryPoint = initialSplit.Blocks[0];
      var blockAssignments = PickBlocksToVerify(initialSplit.Blocks, splitPoints);
      var entryBlockHasSplit = splitPoints.Keys.Contains(entryPoint);
      var baseSplitBlocks = BlockTransformations.PostProcess(DoPreAssignedManualSplit(initialSplit.Options, initialSplit.Blocks, blockAssignments, -1, entryPoint, !entryBlockHasSplit, splitOnEveryAssert));
      splits.Add(new Split(initialSplit.Options, baseSplitBlocks, initialSplit.GotoCmdOrigins, initialSplit.parent, initialSplit.Run));
      foreach (KeyValuePair<Block, int> pair in splitPoints)
      {
        for (int i = 0; i < pair.Value; i++)
        {
          bool lastSplitInBlock = i == pair.Value - 1;
          var newBlocks = DoPreAssignedManualSplit(initialSplit.Options, initialSplit.Blocks, blockAssignments, i, pair.Key, lastSplitInBlock, splitOnEveryAssert);
          splits.Add(new Split(initialSplit.Options, BlockTransformations.PostProcess(newBlocks), initialSplit.GotoCmdOrigins, initialSplit.parent, initialSplit.Run)); // REVIEW: Does gotoCmdOrigins need to be changed at all?
        }
      }
    }
    return splits;
  }

  private static bool ShouldSplitHere(Cmd c, bool splitOnEveryAssert) {
    return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "split_here")
           || c is AssertCmd && splitOnEveryAssert;
  }
  

  // Verify b with the last split in blockAssignments[b]

  private static Dictionary<Block, Block> PickBlocksToVerify (List<Block> blocks, Dictionary<Block, int> splitPoints)
  {
    var todo = new Stack<Block>();
    var blockAssignments = new Dictionary<Block, Block>();
    var immediateDominator = (Program.GraphFromBlocks(blocks)).ImmediateDominator();
    todo.Push(blocks[0]);
    while(todo.Count > 0)
    {
      var currentBlock = todo.Pop();
      if (blockAssignments.Keys.Contains(currentBlock))
      {
        continue;
      }
      else if (immediateDominator[currentBlock] == currentBlock) // if the currentBlock doesn't have a predecessor.
      {
        blockAssignments[currentBlock] = currentBlock;
      }
      else if (splitPoints.Keys.Contains(immediateDominator[currentBlock])) // if the currentBlock's dominator has a split then it will be associated with that split
      {
        blockAssignments[currentBlock] = immediateDominator[currentBlock];
      }
      else
      {
        Contract.Assert(blockAssignments.Keys.Contains(immediateDominator[currentBlock]));
        blockAssignments[currentBlock] = blockAssignments[immediateDominator[currentBlock]];
      }
      if (currentBlock.TransferCmd is GotoCmd exit)
      {
        exit.labelTargets.ForEach(blk => todo.Push(blk));
      }
    }
    return blockAssignments;
  }

  private static List<Block> DoPreAssignedManualSplit(VCGenOptions options, List<Block> blocks, Dictionary<Block, Block> blockAssignments, int splitNumberWithinBlock,
    Block containingBlock, bool lastSplitInBlock, bool splitOnEveryAssert)
  {
    var newBlocks = new List<Block>(blocks.Count()); // Copies of the original blocks
    var duplicator = new Duplicator();
    var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count()); // Maps original blocks to their new copies in newBlocks
    foreach (var currentBlock in blocks)
    {
      var newBlock = (Block)duplicator.VisitBlock(currentBlock);
      oldToNewBlockMap[currentBlock] = newBlock;
      newBlocks.Add(newBlock);
      if (currentBlock == containingBlock)
      {
        var newCmds = new List<Cmd>();
        var splitCount = -1;
        var verify = splitCount == splitNumberWithinBlock;
        foreach (Cmd c in currentBlock.Cmds)
        {
          if (ShouldSplitHere(c, splitOnEveryAssert))
          {
            splitCount++;
            verify = splitCount == splitNumberWithinBlock;
          }
          newCmds.Add(verify ? c : CommandTransformations.AssertIntoAssume(options, c));
        }
        newBlock.Cmds = newCmds;
      }
      else if (lastSplitInBlock && blockAssignments[currentBlock] == containingBlock)
      {
        var verify = true;
        var newCmds = new List<Cmd>();
        foreach(Cmd c in currentBlock.Cmds) {
          verify = !ShouldSplitHere(c, splitOnEveryAssert) && verify;
          newCmds.Add(verify ? c : CommandTransformations.AssertIntoAssume(options, c));
        }
        newBlock.Cmds = newCmds;
      }
      else
      {
        newBlock.Cmds = currentBlock.Cmds.Select<Cmd, Cmd>(x => CommandTransformations.AssertIntoAssume(options, x)).ToList();
      }
    }
    // Patch the edges between the new blocks
    foreach (var oldBlock in blocks)
    {
      if (oldBlock.TransferCmd is ReturnCmd)
      {
        continue;
      }

      var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
      var newLabelTargets = new List<Block>(gotoCmd.labelTargets.Count());
      var newLabelNames = new List<string>(gotoCmd.labelTargets.Count());
      foreach (var target in gotoCmd.labelTargets)
      {
        newLabelTargets.Add(oldToNewBlockMap[target]);
        newLabelNames.Add(oldToNewBlockMap[target].Label);
      }

      oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
    }
    return newBlocks;
  }
}