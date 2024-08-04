using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using VC;

namespace VCGeneration;

public static class ManualSplitFinder {
  public static IEnumerable<ManualSplit> FocusAndSplit(VCGenOptions options, ImplementationRun run, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerificationConditionGenerator par) {
    var focussedImpl = FocusAttribute.FocusImpl(options, run, gotoCmdOrigins, par);
    return focussedImpl.SelectMany(FindManualSplits);
  }

  private static List<ManualSplit /*!*/> FindManualSplits(ManualSplit initialSplit) {
    Contract.Requires(initialSplit.Implementation != null);
    Contract.Ensures(Contract.Result<List<Split>>() == null || Cce.NonNullElements(Contract.Result<List<Split>>()));

    var splitOnEveryAssert = initialSplit.Options.VcsSplitOnEveryAssert;
    initialSplit.Run.Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

    var splitPoints = new Dictionary<Block, List<IToken>>();
    foreach (var block in initialSplit.Blocks) {
      foreach (Cmd command in block.Cmds) {
        if (ShouldSplitHere(command, splitOnEveryAssert)) {
          splitPoints.GetOrCreate(block, () => new List<IToken>()).Add(command.tok);
        }
      }
    }
    var splits = new List<ManualSplit>();
    if (!splitPoints.Any()) {
      splits.Add(initialSplit);
    } else {
      Block entryPoint = initialSplit.Blocks[0];
      var blockAssignments = PickBlocksToVerify(initialSplit.Blocks, splitPoints);
      var entryBlockHasSplit = splitPoints.ContainsKey(entryPoint);
      var baseSplitBlocks = BlockTransformations.DeleteNoAssertionBlocks(
        DoPreAssignedManualSplit(initialSplit.Options, initialSplit.Blocks, blockAssignments,
          -1, entryPoint, !entryBlockHasSplit, splitOnEveryAssert));
      splits.Add(new ManualSplit(initialSplit.Options, baseSplitBlocks, initialSplit.GotoCmdOrigins, initialSplit.parent, initialSplit.Run, initialSplit.Token));
      foreach (var block in initialSplit.Blocks) {
        var tokens = splitPoints.GetValueOrDefault(block);
        if (tokens == null) {
          continue;
        }
        
        for (int i = 0; i < tokens.Count; i++) {
          var token = tokens[i];
          bool lastSplitInBlock = i == tokens.Count - 1;
          var newBlocks = DoPreAssignedManualSplit(initialSplit.Options, initialSplit.Blocks, blockAssignments, i, block, lastSplitInBlock, splitOnEveryAssert);
          splits.Add(new ManualSplit(initialSplit.Options, 
            BlockTransformations.DeleteNoAssertionBlocks(newBlocks), initialSplit.GotoCmdOrigins, initialSplit.parent, initialSplit.Run, token));
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
  private static Dictionary<Block, Block> PickBlocksToVerify(List<Block> blocks, Dictionary<Block, List<IToken>> splitPoints) {
    var todo = new Stack<Block>();
    var blockAssignments = new Dictionary<Block, Block>();
    var immediateDominator = Program.GraphFromBlocks(blocks).ImmediateDominator();
    todo.Push(blocks[0]);
    while (todo.Count > 0) {
      var currentBlock = todo.Pop();
      if (blockAssignments.Keys.Contains(currentBlock)) {
        continue;
      }

      if (immediateDominator[currentBlock] == currentBlock) // if the currentBlock doesn't have a predecessor.
      {
        blockAssignments[currentBlock] = currentBlock;
      } else if (splitPoints.ContainsKey(immediateDominator[currentBlock])) // if the currentBlock's dominator has a split then it will be associated with that split
      {
        blockAssignments[currentBlock] = immediateDominator[currentBlock];
      } else {
        Contract.Assert(blockAssignments.Keys.Contains(immediateDominator[currentBlock]));
        blockAssignments[currentBlock] = blockAssignments[immediateDominator[currentBlock]];
      }
      if (currentBlock.TransferCmd is GotoCmd exit) {
        exit.labelTargets.ForEach(blk => todo.Push(blk));
      }
    }
    return blockAssignments;
  }

  private static List<Block> DoPreAssignedManualSplit(VCGenOptions options, List<Block> blocks, Dictionary<Block, Block> blockAssignments, int splitNumberWithinBlock,
    Block containingBlock, bool lastSplitInBlock, bool splitOnEveryAssert) {
    var newBlocks = new List<Block>(blocks.Count); // Copies of the original blocks
    //var duplicator = new Duplicator();
    var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count); // Maps original blocks to their new copies in newBlocks
    foreach (var currentBlock in blocks) {
      var newBlock = new Block();
      newBlock.Label = currentBlock.Label;
      newBlock.tok = currentBlock.tok;
      
      oldToNewBlockMap[currentBlock] = newBlock;
      newBlocks.Add(newBlock);
      if (currentBlock == containingBlock) {
        var newCmds = new List<Cmd>();
        var splitCount = -1;
        var verify = splitCount == splitNumberWithinBlock;
        foreach (Cmd command in currentBlock.Cmds) {
          if (ShouldSplitHere(command, splitOnEveryAssert)) {
            splitCount++;
            verify = splitCount == splitNumberWithinBlock;
          }
          newCmds.Add(verify ? command : CommandTransformations.AssertIntoAssume(options, command));
        }
        newBlock.Cmds = newCmds;
      } else if (lastSplitInBlock && blockAssignments[currentBlock] == containingBlock) {
        var verify = true;
        var newCmds = new List<Cmd>();
        foreach (Cmd command in currentBlock.Cmds) {
          verify = !ShouldSplitHere(command, splitOnEveryAssert) && verify;
          newCmds.Add(verify ? command : CommandTransformations.AssertIntoAssume(options, command));
        }
        newBlock.Cmds = newCmds;
      } else {
        newBlock.Cmds = currentBlock.Cmds.Select(x => CommandTransformations.AssertIntoAssume(options, x)).ToList();
      }
    }
    // Patch the edges between the new blocks
    foreach (var oldBlock in blocks) {
      if (oldBlock.TransferCmd is ReturnCmd) {
        continue;
      }

      var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
      var newLabelTargets = new List<Block>(gotoCmd.labelTargets.Count());
      var newLabelNames = new List<string>(gotoCmd.labelTargets.Count());
      foreach (var target in gotoCmd.labelTargets) {
        newLabelTargets.Add(oldToNewBlockMap[target]);
        newLabelNames.Add(oldToNewBlockMap[target].Label);
      }

      oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
    }
    return newBlocks;
  }
}