using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.GraphUtil;
using Set = Microsoft.Boogie.GSet<object>;

namespace Microsoft.Boogie;

public class LoopExtractor {

    /// <summary>
    /// Used by Corral and Dafny.
    /// </summary>
  public static (Dictionary<string, Dictionary<string, Block>> loops, HashSet<Implementation> procsWithIrreducibleLoops)
    ExtractLoops(CoreOptions options, Program program)
  {
    var hasIrreducibleLoops = new HashSet<Implementation>();
    List<Implementation /*!*/> /*!*/ loopImpls = new List<Implementation /*!*/>();
    Dictionary<string, Dictionary<string, Block>> fullMap = new Dictionary<string, Dictionary<string, Block>>();
    foreach (var impl in program.Implementations)
    {
      if (impl.Blocks != null && impl.Blocks.Count > 0)
      {
        try
        {
          Graph<Block> g = program.ProcessLoops(options, impl);
          CreateProceduresForLoops(options, impl, g, loopImpls, fullMap);
        }
        catch (Program.IrreducibleLoopException)
        {
          System.Diagnostics.Debug.Assert(!fullMap.ContainsKey(impl.Name));
          fullMap[impl.Name] = null;
          hasIrreducibleLoops.Add(impl);

          if (options.ExtractLoopsUnrollIrreducible)
          {
            // statically unroll loops in this procedure

            // First, build a map of the current blocks
            var origBlocks = new Dictionary<string, Block>();
            foreach (var blk in impl.Blocks)
            {
              origBlocks.Add(blk.Label, blk);
            }

            // unroll
            Block start = impl.Blocks[0];
            impl.Blocks = LoopUnroll.UnrollLoops(start, options.RecursionBound, false);

            // Now construct the "map back" information
            // Resulting block label -> original block
            var blockMap = new Dictionary<string, Block>();
            foreach (var blk in impl.Blocks)
            {
              var sl = LoopUnroll.sanitizeLabel(blk.Label);
              if (sl == blk.Label)
              {
                blockMap.Add(blk.Label, blk);
              }
              else
              {
                Contract.Assert(origBlocks.ContainsKey(sl));
                blockMap.Add(blk.Label, origBlocks[sl]);
              }
            }

            fullMap[impl.Name] = blockMap;
          }
        }
      }
    }

    foreach (Implementation /*!*/ loopImpl in loopImpls)
    {
      Contract.Assert(loopImpl != null);
      program.AddTopLevelDeclaration(loopImpl);
      program.AddTopLevelDeclaration(loopImpl.Proc);
    }

    return (fullMap, hasIrreducibleLoops);
  }

  static void CreateProceduresForLoops(CoreOptions options, Implementation impl, Graph<Block /*!*/> /*!*/ g,
    List<Implementation /*!*/> /*!*/ loopImpls,
    Dictionary<string, Dictionary<string, Block>> fullMap)
  {
    Contract.Requires(impl != null);
    Contract.Requires(Cce.NonNullElements(loopImpls));
    // Enumerate the headers
    // for each header h:
    //   create implementation p_h with
    //     inputs = inputs, outputs, and locals of impl
    //     outputs = outputs and locals of impl
    //     locals = empty set
    //   add call o := p_h(i) at the beginning of the header block
    //   break the back edges whose target is h
    // Enumerate the headers again to create the bodies of p_h
    // for each header h:
    //   compute the loop corresponding to h
    //   make copies of all blocks in the loop for h
    //   delete all target edges that do not go to a block in the loop
    //   create a new entry block and a new return block
    //   add edges from entry block to the loop header and the return block
    //   add calls o := p_h(i) at the end of the blocks that are sources of back edges
    foreach (Block block in impl.Blocks)
    {
      AddToFullMap(fullMap, impl.Name, block.Label, block);
    }

    bool detLoopExtract = options.DeterministicExtractLoops;

    Dictionary<Block /*!*/, List<Variable> /*!*/> /*!*/
      loopHeaderToInputs = new Dictionary<Block /*!*/, List<Variable> /*!*/>();
    Dictionary<Block /*!*/, List<Variable> /*!*/> /*!*/
      loopHeaderToOutputs = new Dictionary<Block /*!*/, List<Variable> /*!*/>();
    Dictionary<Block /*!*/, Dictionary<Variable, Expr> /*!*/> /*!*/
      loopHeaderToSubstMap = new Dictionary<Block /*!*/, Dictionary<Variable, Expr> /*!*/>();
    Dictionary<Block /*!*/, LoopProcedure /*!*/> /*!*/
      loopHeaderToLoopProc = new Dictionary<Block /*!*/, LoopProcedure /*!*/>();
    Dictionary<Block /*!*/, CallCmd /*!*/> /*!*/
      loopHeaderToCallCmd1 = new Dictionary<Block /*!*/, CallCmd /*!*/>();
    Dictionary<Block, CallCmd> loopHeaderToCallCmd2 = new Dictionary<Block, CallCmd>();
    Dictionary<Block, AssignCmd> loopHeaderToAssignCmd = new Dictionary<Block, AssignCmd>();

    foreach (Block /*!*/ header in g.Headers)
    {
      Contract.Assert(header != null);
      Contract.Assert(header != null);
      List<Variable> inputs = new List<Variable>();
      List<Variable> outputs = new List<Variable>();
      List<Expr> callInputs1 = new List<Expr>();
      List<IdentifierExpr> callOutputs1 = new List<IdentifierExpr>();
      List<Expr> callInputs2 = new List<Expr>();
      List<IdentifierExpr> callOutputs2 = new List<IdentifierExpr>();
      List<AssignLhs> lhss = new List<AssignLhs>();
      List<Expr> rhss = new List<Expr>();
      Dictionary<Variable, Expr> substMap = new Dictionary<Variable, Expr>(); // Variable -> IdentifierExpr

      List<Variable> /*!*/
        targets = new List<Variable>();
      HashSet<Variable> footprint = new HashSet<Variable>();

      foreach (Block /*!*/ b in g.BackEdgeNodes(header))
      {
        Contract.Assert(b != null);
        HashSet<Block> immSuccBlks = new HashSet<Block>();
        if (detLoopExtract)
        {
          //Need to get the blocks that exit the loop, as we need to add them to targets and footprint
          immSuccBlks = GetBreakBlocksOfLoop(options, header, b, g);
        }

        foreach (Block /*!*/ block in g.NaturalLoops(header, b).Union(immSuccBlks))
        {
          Contract.Assert(block != null);
          foreach (Cmd /*!*/ cmd in block.Cmds)
          {
            Contract.Assert(cmd != null);
            cmd.AddAssignedVariables(targets);

            VariableCollector c = new VariableCollector();
            c.Visit(cmd);
            footprint.UnionWith(c.usedVars);
          }
        }
      }

      List<IdentifierExpr> /*!*/
        globalMods = new List<IdentifierExpr>();
      Set targetSet = new Set();
      foreach (Variable /*!*/ v in targets)
      {
        Contract.Assert(v != null);
        if (targetSet.Contains(v))
        {
          continue;
        }

        targetSet.Add(v);
        if (v is GlobalVariable)
        {
          globalMods.Add(new IdentifierExpr(Token.NoToken, v));
        }
      }

      foreach (Variable v in impl.InParams)
      {
        Contract.Assert(v != null);
        if (!footprint.Contains(v))
        {
          continue;
        }

        callInputs1.Add(new IdentifierExpr(Token.NoToken, v));
        Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in_" + v.Name, v.TypedIdent.Type), true);
        inputs.Add(f);
        callInputs2.Add(new IdentifierExpr(Token.NoToken, f));
        substMap[v] = new IdentifierExpr(Token.NoToken, f);
      }

      foreach (Variable v in impl.OutParams)
      {
        Contract.Assert(v != null);
        if (!footprint.Contains(v))
        {
          continue;
        }

        callInputs1.Add(new IdentifierExpr(Token.NoToken, v));
        Formal f1 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in_" + v.Name, v.TypedIdent.Type), true);
        inputs.Add(f1);
        if (targetSet.Contains(v))
        {
          callOutputs1.Add(new IdentifierExpr(Token.NoToken, v));
          Formal f2 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out_" + v.Name, v.TypedIdent.Type),
            false);
          outputs.Add(f2);
          callInputs2.Add(new IdentifierExpr(Token.NoToken, f2));
          callOutputs2.Add(new IdentifierExpr(Token.NoToken, f2));
          lhss.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, f2)));
          rhss.Add(new IdentifierExpr(Token.NoToken, f1));
          substMap[v] = new IdentifierExpr(Token.NoToken, f2);
        }
        else
        {
          callInputs2.Add(new IdentifierExpr(Token.NoToken, f1));
          substMap[v] = new IdentifierExpr(Token.NoToken, f1);
        }
      }

      foreach (Variable v in impl.LocVars)
      {
        Contract.Assert(v != null);
        if (!footprint.Contains(v))
        {
          continue;
        }

        callInputs1.Add(new IdentifierExpr(Token.NoToken, v));
        Formal f1 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "in_" + v.Name, v.TypedIdent.Type), true);
        inputs.Add(f1);
        if (targetSet.Contains(v))
        {
          callOutputs1.Add(new IdentifierExpr(Token.NoToken, v));
          Formal f2 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "out_" + v.Name, v.TypedIdent.Type),
            false);
          outputs.Add(f2);
          callInputs2.Add(new IdentifierExpr(Token.NoToken, f2));
          callOutputs2.Add(new IdentifierExpr(Token.NoToken, f2));
          lhss.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, f2)));
          rhss.Add(new IdentifierExpr(Token.NoToken, f1));
          substMap[v] = new IdentifierExpr(Token.NoToken, f2);
        }
        else
        {
          callInputs2.Add(new IdentifierExpr(Token.NoToken, f1));
          substMap[v] = new IdentifierExpr(Token.NoToken, f1);
        }
      }

      loopHeaderToInputs[header] = inputs;
      loopHeaderToOutputs[header] = outputs;
      loopHeaderToSubstMap[header] = substMap;
      LoopProcedure loopProc = new LoopProcedure(impl, header, inputs, outputs, globalMods);
      loopHeaderToLoopProc[header] = loopProc;

      CallCmd callCmd1 = new CallCmd(Token.NoToken, loopProc.Name, callInputs1, callOutputs1);
      callCmd1.Proc = loopProc;
      loopHeaderToCallCmd1[header] = callCmd1;

      CallCmd callCmd2 = new CallCmd(Token.NoToken, loopProc.Name, callInputs2, callOutputs2);
      callCmd2.Proc = loopProc;
      loopHeaderToCallCmd2[header] = callCmd2;

      Debug.Assert(lhss.Count == rhss.Count);
      if (lhss.Count > 0)
      {
        AssignCmd assignCmd = new AssignCmd(Token.NoToken, lhss, rhss);
        loopHeaderToAssignCmd[header] = assignCmd;
      }
    }

    // Keep track of the new blocks created: maps a header node to the
    // header_last block that was created because of splitting header.
    Dictionary<Block, Block> newBlocksCreated = new Dictionary<Block, Block>();

    bool headRecursion = false; // testing an option to put recursive call before loop body

    IEnumerable<Block> sortedHeaders = g.SortHeadersByDominance();
    foreach (Block /*!*/ header in sortedHeaders)
    {
      Contract.Assert(header != null);
      LoopProcedure loopProc = loopHeaderToLoopProc[header];
      Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
      HashSet<string> dummyBlocks = new HashSet<string>();

      var subst = Substituter.SubstitutionFromDictionary(loopHeaderToSubstMap[header]); // fix me
      List<Variable> inputs = loopHeaderToInputs[header];
      List<Variable> outputs = loopHeaderToOutputs[header];
      int si_unique_loc = 1; // Added by AL: to distinguish the back edges
      foreach (Block /*!*/ source in g.BackEdgeNodes(header))
      {
        Contract.Assert(source != null);
        foreach (Block /*!*/ block in g.NaturalLoops(header, source))
        {
          Contract.Assert(block != null);
          if (blockMap.ContainsKey(block))
          {
            continue;
          }

          Block newBlock = new Block();
          newBlock.Label = block.Label;
          if (headRecursion && block == header)
          {
            CallCmd callCmd = (CallCmd) (loopHeaderToCallCmd2[header]).Clone();
            addUniqueCallAttr(si_unique_loc, callCmd);
            si_unique_loc++;
            newBlock.Cmds.Add(callCmd); // add the recursive call at head of loop
            var rest = Substituter.Apply(subst, block.Cmds);
            newBlock.Cmds.AddRange(rest);
          }
          else
          {
            newBlock.Cmds = Substituter.Apply(subst, block.Cmds);
          }

          blockMap[block] = newBlock;
          if (newBlocksCreated.ContainsKey(block))
          {
            Block newBlock2 = new Block();
            newBlock2.Label = newBlocksCreated[block].Label;
            newBlock2.Cmds = Substituter.Apply(subst, newBlocksCreated[block].Cmds);
            blockMap[newBlocksCreated[block]] = newBlock2;
          }

          //for detLoopExtract, need the immediate successors even outside the loop
          if (detLoopExtract)
          {
            GotoCmd auxGotoCmd = block.TransferCmd as GotoCmd;
            Contract.Assert(auxGotoCmd != null && auxGotoCmd.labelNames != null &&
                            auxGotoCmd.labelTargets != null && auxGotoCmd.labelTargets.Count >= 1);
            //BUGFIX on 10/26/15: this contains nodes present in NaturalLoops for a different backedgenode
            var loopNodes = GetBlocksInAllNaturalLoops(options, header, g); //var loopNodes = g.NaturalLoops(header, source);
            foreach (var bl in auxGotoCmd.labelTargets)
            {
              if (g.Nodes.Contains(bl) && //newly created blocks are not present in NaturalLoop(header, xx, g)
                  !loopNodes.Contains(bl))
              {
                Block auxNewBlock = new Block();
                auxNewBlock.Label = bl.Label;
                //these blocks may have read/write locals that are not present in naturalLoops
                //we need to capture these variables
                auxNewBlock.Cmds = Substituter.Apply(subst, bl.Cmds);
                //add restoration code for such blocks
                if (loopHeaderToAssignCmd.ContainsKey(header))
                {
                  AssignCmd assignCmd = loopHeaderToAssignCmd[header];
                  auxNewBlock.Cmds.Add(assignCmd);
                }

                List<AssignLhs> lhsg = new List<AssignLhs>();
                List<IdentifierExpr> /*!*/
                  globalsMods = loopHeaderToLoopProc[header].Modifies;
                foreach (IdentifierExpr gl in globalsMods)
                {
                  lhsg.Add(new SimpleAssignLhs(Token.NoToken, gl));
                }

                List<Expr> rhsg = new List<Expr>();
                foreach (IdentifierExpr gl in globalsMods)
                {
                  rhsg.Add(new OldExpr(Token.NoToken, gl));
                }

                if (lhsg.Count != 0)
                {
                  AssignCmd globalAssignCmd = new AssignCmd(Token.NoToken, lhsg, rhsg);
                  auxNewBlock.Cmds.Add(globalAssignCmd);
                }

                blockMap[(Block) bl] = auxNewBlock;
              }
            }
          }
        }

        List<Cmd> cmdSeq;
        if (headRecursion)
        {
          cmdSeq = new List<Cmd>();
        }
        else
        {
          CallCmd callCmd = (CallCmd) (loopHeaderToCallCmd2[header]).Clone();
          addUniqueCallAttr(si_unique_loc, callCmd);
          si_unique_loc++;
          cmdSeq = new List<Cmd> {callCmd};
        }

        Block /*!*/
          block1 = new Block(Token.NoToken, source.Label + "_dummy",
            new List<Cmd> {new AssumeCmd(Token.NoToken, Expr.False)}, new ReturnCmd(Token.NoToken));
        Block /*!*/
          block2 = new Block(Token.NoToken, block1.Label,
            cmdSeq, new ReturnCmd(Token.NoToken));
        impl.Blocks.Add(block1);
        dummyBlocks.Add(block1.Label);

        GotoCmd gotoCmd = source.TransferCmd as GotoCmd;
        Contract.Assert(gotoCmd != null && gotoCmd.labelNames != null && gotoCmd.labelTargets != null &&
                        gotoCmd.labelTargets.Count >= 1);
        List<String> /*!*/
          newLabels = new List<String>();
        List<Block> /*!*/
          newTargets = new List<Block>();
        for (int i = 0; i < gotoCmd.labelTargets.Count; i++)
        {
          if (gotoCmd.labelTargets[i] == header)
          {
            continue;
          }

          newTargets.Add(gotoCmd.labelTargets[i]);
          newLabels.Add(gotoCmd.labelNames[i]);
        }

        newTargets.Add(block1);
        newLabels.Add(block1.Label);
        gotoCmd.labelNames = newLabels;
        gotoCmd.labelTargets = newTargets;
        blockMap[block1] = block2;
      }

      List<Block /*!*/> /*!*/
        blocks = new List<Block /*!*/>();
      Block exit = new Block(Token.NoToken, "exit", new List<Cmd>(), new ReturnCmd(Token.NoToken));
      GotoCmd cmd = new GotoCmd(Token.NoToken,
        new List<String> {Cce.NonNull(blockMap[header]).Label, exit.Label},
        new List<Block> {blockMap[header], exit});

      if (detLoopExtract) //cutting the non-determinism
      {
        cmd = new GotoCmd(Token.NoToken,
          new List<String> {Cce.NonNull(blockMap[header]).Label},
          new List<Block> {blockMap[header]});
      }

      Block entry;
      List<Cmd> initCmds = new List<Cmd>();
      if (loopHeaderToAssignCmd.ContainsKey(header))
      {
        AssignCmd assignCmd = loopHeaderToAssignCmd[header];
        initCmds.Add(assignCmd);
      }

      entry = new Block(Token.NoToken, "entry", initCmds, cmd);
      blocks.Add(entry);

      foreach (Block /*!*/ block in blockMap.Keys)
      {
        Contract.Assert(block != null);
        Block /*!*/
          newBlock = Cce.NonNull(blockMap[block]);
        GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
        if (gotoCmd == null)
        {
          newBlock.TransferCmd = new ReturnCmd(Token.NoToken);
        }
        else
        {
          Contract.Assume(gotoCmd.labelNames != null && gotoCmd.labelTargets != null);
          List<String> newLabels = new List<String>();
          List<Block> newTargets = new List<Block>();
          for (int i = 0; i < gotoCmd.labelTargets.Count; i++)
          {
            Block target = gotoCmd.labelTargets[i];
            if (blockMap.ContainsKey(target))
            {
              newLabels.Add(gotoCmd.labelNames[i]);
              newTargets.Add(blockMap[target]);
            }
          }

          if (newTargets.Count == 0)
          {
            if (!detLoopExtract)
            {
              newBlock.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            }

            newBlock.TransferCmd = new ReturnCmd(Token.NoToken);
          }
          else
          {
            newBlock.TransferCmd = new GotoCmd(Token.NoToken, newLabels, newTargets);
          }
        }

        blocks.Add(newBlock);
      }

      blocks.Add(exit);
      Implementation loopImpl =
        new Implementation(Token.NoToken, loopProc.Name,
          new List<TypeVariable>(), inputs, outputs, new List<Variable>(), blocks);
      loopImpl.Proc = loopProc;
      loopImpls.Add(loopImpl);

      // Make a (shallow) copy of the header before splitting it
      Block origHeader = new Block(header.tok, header.Label, header.Cmds, header.TransferCmd);

      // Finally, add call to the loop in the containing procedure
      string lastIterBlockName = header.Label + "_last";
      Block lastIterBlock = new Block(Token.NoToken, lastIterBlockName, header.Cmds, header.TransferCmd);
      newBlocksCreated[header] = lastIterBlock;
      header.Cmds = new List<Cmd> {loopHeaderToCallCmd1[header]};
      header.TransferCmd = new GotoCmd(Token.NoToken, new List<String> {lastIterBlockName},
        new List<Block> {lastIterBlock});
      impl.Blocks.Add(lastIterBlock);
      blockMap[origHeader] = blockMap[header];
      blockMap.Remove(header);

      Contract.Assert(fullMap[impl.Name][header.Label] == header);
      fullMap[impl.Name][header.Label] = origHeader;

      foreach (Block block in blockMap.Keys)
      {
        // Don't add dummy blocks to the map
        if (dummyBlocks.Contains(blockMap[block].Label))
        {
          continue;
        }

        // Following two statements are for nested loops: compose map
        if (!fullMap[impl.Name].ContainsKey(block.Label))
        {
          continue;
        }

        var target = fullMap[impl.Name][block.Label];

        AddToFullMap(fullMap, loopProc.Name, blockMap[block].Label, target);
      }

      fullMap[impl.Name].Remove(header.Label);
      fullMap[impl.Name][lastIterBlockName] = origHeader;
    }
  }

  private static void addUniqueCallAttr(int val, CallCmd cmd)
  {
    var a = new List<object>();
    a.Add(new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(val)));

    cmd.Attributes = new QKeyValue(Token.NoToken, "si_unique_call", a, cmd.Attributes);
  }

  private static void AddToFullMap(Dictionary<string, Dictionary<string, Block>> fullMap, string procName, string blockName,
    Block block)
  {
    if (!fullMap.ContainsKey(procName))
    {
      fullMap[procName] = new Dictionary<string, Block>();
    }

    fullMap[procName][blockName] = block;
  }

  private static HashSet<Block> GetBlocksInAllNaturalLoops(CoreOptions options, Block header, Graph<Block /*!*/> /*!*/ g)
  {
    Contract.Assert(options.DeterministicExtractLoops,
      "Can only be called with /deterministicExtractLoops option");
    var allBlocksInNaturalLoops = new HashSet<Block>();
    foreach (Block /*!*/ source in g.BackEdgeNodes(header))
    {
      Contract.Assert(source != null);
      g.NaturalLoops(header, source).ForEach(b => allBlocksInNaturalLoops.Add(b));
    }

    return allBlocksInNaturalLoops;
  }


  /// <summary>
  /// Finds blocks that break out of a loop in NaturalLoops(header, backEdgeNode)
  /// </summary>
  /// <param name="header"></param>
  /// <param name="backEdgeNode"></param>
  /// <returns></returns>
  private static HashSet<Block> GetBreakBlocksOfLoop(CoreOptions options, Block header, Block backEdgeNode, Graph<Block /*!*/> /*!*/ g)
  {
    Contract.Assert(options.DeterministicExtractLoops,
      "Can only be called with /deterministicExtractLoops option");
    var immSuccBlks = new HashSet<Block>();
    var loopBlocks = g.NaturalLoops(header, backEdgeNode);
    foreach (Block /*!*/ block in loopBlocks)
    {
      Contract.Assert(block != null);
      var auxCmd = block.TransferCmd as GotoCmd;
      if (auxCmd == null)
      {
        continue;
      }

      foreach (var bl in auxCmd.labelTargets)
      {
        if (loopBlocks.Contains(bl))
        {
          continue;
        }

        immSuccBlks.Add(bl);
      }
    }

    return immSuccBlks;
  }
}