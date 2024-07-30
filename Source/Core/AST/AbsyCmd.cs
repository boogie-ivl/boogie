using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using Set = Microsoft.Boogie.GSet<object>;

namespace Microsoft.Boogie
{
  //---------------------------------------------------------------------
  // BigBlock
  public class BigBlock
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(tok != null);
      Contract.Invariant(Anonymous || this.labelName != null);
      Contract.Invariant(this._ec == null || this._tc == null);
      Contract.Invariant(this._simpleCmds != null);
    }

    public readonly IToken /*!*/
      tok;

    public readonly bool Anonymous;

    private string labelName;

    public string LabelName
    {
      get
      {
        Contract.Ensures(Anonymous || Contract.Result<string>() != null);
        return this.labelName;
      }
      set
      {
        Contract.Requires(Anonymous || value != null);
        this.labelName = value;
      }
    }

    [Rep] private List<Cmd> /*!*/ _simpleCmds;

    /// <summary>
    /// These come before the structured command
    /// </summary>
    public List<Cmd> /*!*/ simpleCmds
    {
      get
      {
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);
        return this._simpleCmds;
      }
      set
      {
        Contract.Requires(value != null);
        this._simpleCmds = value;
      }
    }

    private StructuredCmd _ec;

    public StructuredCmd ec
    {
      get { return this._ec; }
      set
      {
        Contract.Requires(value == null || this.tc == null);
        this._ec = value;
      }
    }

    private TransferCmd _tc;

    public TransferCmd tc
    {
      get { return this._tc; }
      set
      {
        Contract.Requires(value == null || this.ec == null);
        this._tc = value;
      }
    }

    public BigBlock
      successorBigBlock; // semantic successor (may be a back-edge, pointing back to enclosing while statement); null if successor is end of procedure body (or if field has not yet been initialized)

    public BigBlock(IToken tok, string labelName, [Captured] List<Cmd> simpleCmds, StructuredCmd ec, TransferCmd tc)
    {
      Contract.Requires(simpleCmds != null);
      Contract.Requires(tok != null);
      Contract.Requires(ec == null || tc == null);
      this.tok = tok;
      this.Anonymous = labelName == null;
      this.labelName = labelName;
      this._simpleCmds = simpleCmds;
      this._ec = ec;
      this._tc = tc;
    }

    public void Emit(TokenTextWriter stream, int level)
    {
      Contract.Requires(stream != null);
      if (!Anonymous)
      {
        stream.WriteLine(level, "{0}:",
          stream.Options.PrintWithUniqueASTIds
            ? String.Format("h{0}^^{1}", this.GetHashCode(), this.LabelName)
            : this.LabelName);
      }

      foreach (Cmd /*!*/ c in this.simpleCmds)
      {
        Contract.Assert(c != null);
        c.Emit(stream, level + 1);
      }

      if (this.ec != null)
      {
        this.ec.Emit(stream, level + 1);
      }
      else if (this.tc != null)
      {
        this.tc.Emit(stream, level + 1);
      }
    }
  }

  public class StmtList
  {
    [Rep] private readonly List<BigBlock /*!*/> /*!*/ bigBlocks;

    public IList<BigBlock /*!*/> /*!*/ BigBlocks
    {
      get
      {
        Contract.Ensures(Contract.Result<IList<BigBlock>>() != null);
        Contract.Ensures(Contract.Result<IList<BigBlock>>().IsReadOnly);
        return this.bigBlocks.AsReadOnly();
      }
    }

    public List<Cmd> PrefixCommands;

    public readonly IToken /*!*/
      EndCurly;

    public StmtList ParentContext;
    public BigBlock ParentBigBlock;

    private readonly HashSet<string /*!*/> /*!*/
      labels = new HashSet<string /*!*/>();

    public void AddLabel(string label)
    {
      labels.Add(label);
    }

    public IEnumerable<string /*!*/> /*!*/ Labels
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<string /*!*/> /*!*/>()));
        return this.labels.AsEnumerable<string>();
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(EndCurly != null);
      Contract.Invariant(cce.NonNullElements(this.bigBlocks));
      Contract.Invariant(cce.NonNullElements(this.labels));
    }

    public StmtList(IList<BigBlock /*!*/> /*!*/ bigblocks, IToken endCurly)
    {
      Contract.Requires(endCurly != null);
      Contract.Requires(cce.NonNullElements(bigblocks));
      Contract.Requires(bigblocks.Count > 0);
      this.bigBlocks = new List<BigBlock>(bigblocks);
      this.EndCurly = endCurly;
    }

    // prints the list of statements, not the surrounding curly braces
    public void Emit(TokenTextWriter stream, int level)
    {
      Contract.Requires(stream != null);
      bool needSeperator = false;
      foreach (BigBlock b in BigBlocks)
      {
        Contract.Assert(b != null);
        Contract.Assume(cce.IsPeerConsistent(b));
        if (needSeperator)
        {
          stream.WriteLine();
        }

        b.Emit(stream, level);
        needSeperator = true;
      }
    }

    /// <summary>
    /// Tries to insert the commands "prefixCmds" at the beginning of the first block
    /// of the StmtList, and returns "true" iff it succeeded.
    /// In the event of success, the "suggestedLabel" returns as the name of the
    /// block inside StmtList where "prefixCmds" were inserted.  This name may be the
    /// same as the one passed in, in case this StmtList has no preference as to what
    /// to call its first block.  In the event of failure, "suggestedLabel" is returned
    /// as its input value.
    /// Note, to be conservative (that is, ignoring the possible optimization that this
    /// method enables), this method can do nothing and return false.
    /// </summary>
    public bool PrefixFirstBlock([Captured] List<Cmd> prefixCmds, ref string suggestedLabel)
    {
      Contract.Requires(suggestedLabel != null);
      Contract.Requires(prefixCmds != null);
      Contract.Ensures(Contract.Result<bool>() ||
                       cce.Owner.None(prefixCmds)); // "prefixCmds" is captured only on success
      Contract.Assume(PrefixCommands == null); // prefix has not been used

      BigBlock bb0 = BigBlocks[0];
      if (prefixCmds.Count == 0)
      {
        // This is always a success, since there is nothing to insert.  Now, decide
        // which name to use for the first block.
        if (bb0.Anonymous)
        {
          bb0.LabelName = suggestedLabel;
        }
        else
        {
          Contract.Assert(bb0.LabelName != null);
          suggestedLabel = bb0.LabelName;
        }

        return true;
      }
      else
      {
        // There really is something to insert.  We can do this inline only if the first
        // block is anonymous (which implies there is no branch to it from within the block).
        if (bb0.Anonymous)
        {
          PrefixCommands = prefixCmds;
          bb0.LabelName = suggestedLabel;
          return true;
        }
        else
        {
          return false;
        }
      }
    }
  }

  /// <summary>
  /// The AST for Boogie structured commands was designed to support backward compatibility with
  /// the Boogie unstructured commands.  This has made the structured commands hard to construct.
  /// The StmtListBuilder class makes it easier to build structured commands.
  /// </summary>
  public class StmtListBuilder
  {
    readonly List<BigBlock /*!*/> /*!*/ bigBlocks = new();

    string label;
    List<Cmd> simpleCmds;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullElements(bigBlocks));
    }

    void Dump(StructuredCmd scmd, TransferCmd tcmd)
    {
      Contract.Requires(scmd == null || tcmd == null);
      Contract.Ensures(label == null && simpleCmds == null);
      if (label == null && simpleCmds == null && scmd == null && tcmd == null)
      {
        // nothing to do
      }
      else
      {
        if (simpleCmds == null)
        {
          simpleCmds = new List<Cmd>();
        }

        bigBlocks.Add(new BigBlock(Token.NoToken, label, simpleCmds, scmd, tcmd));
        label = null;
        simpleCmds = null;
      }
    }

    /// <summary>
    /// Collects the StmtList built so far and returns it.  The StmtListBuilder should no longer
    /// be used once this method has been invoked.
    /// </summary>
    public StmtList Collect(IToken endCurlyBrace)
    {
      Contract.Requires(endCurlyBrace != null);
      Contract.Ensures(Contract.Result<StmtList>() != null);
      Dump(null, null);
      if (bigBlocks.Count == 0)
      {
        simpleCmds = new List<Cmd>(); // the StmtList constructor doesn't like an empty list of BigBlock's
        Dump(null, null);
      }

      return new StmtList(bigBlocks, endCurlyBrace);
    }

    public void Add(Cmd cmd)
    {
      Contract.Requires(cmd != null);
      if (simpleCmds == null)
      {
        simpleCmds = new List<Cmd>();
      }

      simpleCmds.Add(cmd);
    }

    public void Add(StructuredCmd scmd)
    {
      Contract.Requires(scmd != null);
      Dump(scmd, null);
    }

    public void Add(TransferCmd tcmd)
    {
      Contract.Requires(tcmd != null);
      Dump(null, tcmd);
    }

    public void AddLabelCmd(string label)
    {
      Contract.Requires(label != null);
      Dump(null, null);
      this.label = label;
    }

    public void AddLocalVariable(string name)
    {
      Contract.Requires(name != null);
      // TODO
    }
  }

  class BigBlocksResolutionContext
  {
    StmtList /*!*/
      stmtList;

    [Peer] List<Block /*!*/> blocks;

    string /*!*/
      prefix = "anon";

    int anon = 0;

    int FreshAnon()
    {
      return anon++;
    }

    HashSet<string /*!*/> allLabels = new HashSet<string /*!*/>();

    Errors /*!*/
      errorHandler;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(stmtList != null);
      Contract.Invariant(cce.NonNullElements(blocks, true));
      Contract.Invariant(prefix != null);
      Contract.Invariant(cce.NonNullElements(allLabels, true));
      Contract.Invariant(errorHandler != null);
    }

    private void ComputeAllLabels(StmtList stmts)
    {
      if (stmts == null)
      {
        return;
      }

      foreach (BigBlock bb in stmts.BigBlocks)
      {
        if (bb.LabelName != null)
        {
          allLabels.Add(bb.LabelName);
        }

        ComputeAllLabels(bb.ec);
      }
    }

    private void ComputeAllLabels(StructuredCmd cmd)
    {
      if (cmd == null)
      {
        return;
      }

      if (cmd is IfCmd)
      {
        IfCmd ifCmd = (IfCmd) cmd;
        ComputeAllLabels(ifCmd.thn);
        ComputeAllLabels(ifCmd.elseIf);
        ComputeAllLabels(ifCmd.elseBlock);
      }
      else if (cmd is WhileCmd)
      {
        WhileCmd whileCmd = (WhileCmd) cmd;
        ComputeAllLabels(whileCmd.Body);
      }
    }

    public BigBlocksResolutionContext(StmtList stmtList, Errors errorHandler)
    {
      Contract.Requires(errorHandler != null);
      Contract.Requires(stmtList != null);
      this.stmtList = stmtList;
      // Inject an empty big block at the end of the body of a while loop if its current end is another while loop.
      // This transformation creates a suitable jump target for break statements inside the nested while loop.
      InjectEmptyBigBlockInsideWhileLoopBody(stmtList);
      this.errorHandler = errorHandler;
      ComputeAllLabels(stmtList);
    }

    public List<Block /*!*/> /*!*/ Blocks
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
        if (blocks == null)
        {
          blocks = new List<Block /*!*/>();

          int startErrorCount = this.errorHandler.count;
          // Check that all goto statements go to a label in allLabels, and no break statement to a non-enclosing loop.
          // Also, determine a good value for "prefix".
          CheckLegalLabels(stmtList, null, null);

          // fill in names of anonymous blocks
          NameAnonymousBlocks(stmtList);

          // determine successor blocks
          RecordSuccessors(stmtList, null);

          if (this.errorHandler.count == startErrorCount)
          {
            // generate blocks from the big blocks
            CreateBlocks(stmtList, null);
          }
        }

        return blocks;
      }
    }

    void InjectEmptyBigBlockInsideWhileLoopBody(StmtList stmtList)
    {
      foreach (var bb in stmtList.BigBlocks)
      {
        InjectEmptyBigBlockInsideWhileLoopBody(bb.ec);
      }
    }

    void InjectEmptyBigBlockInsideWhileLoopBody(StructuredCmd structuredCmd)
    {
      if (structuredCmd is WhileCmd whileCmd)
      {
        InjectEmptyBigBlockInsideWhileLoopBody(whileCmd.Body);
        if (whileCmd.Body.BigBlocks.Count > 0 && whileCmd.Body.BigBlocks.Last().ec is WhileCmd)
        {
          var newBigBlocks = new List<BigBlock>(whileCmd.Body.BigBlocks);
          newBigBlocks.Add(new BigBlock(Token.NoToken, null, new List<Cmd>(), null, null));
          whileCmd.Body = new StmtList(newBigBlocks, whileCmd.Body.EndCurly);
        }
      }
      else if (structuredCmd is IfCmd ifCmd)
      {
        InjectEmptyBigBlockInsideWhileLoopBody(ifCmd.thn);
        if (ifCmd.elseBlock != null)
        {
          InjectEmptyBigBlockInsideWhileLoopBody(ifCmd.elseBlock);
        }

        if (ifCmd.elseIf != null)
        {
          InjectEmptyBigBlockInsideWhileLoopBody(ifCmd.elseIf);
        }
      }
    }

    void CheckLegalLabels(StmtList stmtList, StmtList parentContext, BigBlock parentBigBlock)
    {
      Contract.Requires(stmtList != null);
      Contract.Requires((parentContext == null) == (parentBigBlock == null));
      Contract.Requires(stmtList.ParentContext == null); // it hasn't been set yet
      //modifies stmtList.*;
      Contract.Ensures(stmtList.ParentContext == parentContext);
      stmtList.ParentContext = parentContext;
      stmtList.ParentBigBlock = parentBigBlock;

      // record the labels declared in this StmtList
      foreach (BigBlock b in stmtList.BigBlocks)
      {
        if (b.LabelName != null)
        {
          string n = b.LabelName;
          if (n.StartsWith(prefix))
          {
            if (prefix.Length < n.Length && n[prefix.Length] == '0')
            {
              prefix += "1";
            }
            else
            {
              prefix += "0";
            }
          }

          stmtList.AddLabel(b.LabelName);
        }
      }

      // check that labels in this and nested StmtList's are legal
      foreach (BigBlock b in stmtList.BigBlocks)
      {
        // goto's must reference blocks in enclosing blocks
        if (b.tc is GotoCmd)
        {
          GotoCmd g = (GotoCmd) b.tc;
          foreach (string /*!*/ lbl in cce.NonNull(g.labelNames))
          {
            Contract.Assert(lbl != null);
            /*
            bool found = false;
            for (StmtList sl = stmtList; sl != null; sl = sl.ParentContext) {
              if (sl.Labels.Contains(lbl)) {
                found = true;
                break;
              }
            }
            if (!found) {
              this.errorHandler.SemErr(g.tok, "Error: goto label '" + lbl + "' is undefined or out of reach");
            }
            */
            if (!allLabels.Contains(lbl))
            {
              this.errorHandler.SemErr(g.tok, "Error: goto label '" + lbl + "' is undefined");
            }
          }
        }

        // break labels must refer to an enclosing while statement
        else if (b.ec is BreakCmd)
        {
          BreakCmd bcmd = (BreakCmd) b.ec;
          Contract.Assert(bcmd.BreakEnclosure == null); // it hasn't been initialized yet
          bool found = false;
          for (StmtList sl = stmtList; sl.ParentBigBlock != null; sl = sl.ParentContext)
          {
            cce.LoopInvariant(sl != null);
            BigBlock bb = sl.ParentBigBlock;

            if (bcmd.Label == null)
            {
              // a label-less break statement breaks out of the innermost enclosing while statement
              if (bb.ec is WhileCmd)
              {
                bcmd.BreakEnclosure = bb;
                found = true;
                break;
              }
            }
            else if (bcmd.Label == bb.LabelName)
            {
              // a break statement with a label can break out of both if statements and while statements
              if (bb.simpleCmds.Count == 0)
              {
                // this is a good target:  the label refers to the if/while statement
                bcmd.BreakEnclosure = bb;
              }
              else
              {
                // the label of bb refers to the first statement of bb, which in which case is a simple statement, not an if/while statement
                this.errorHandler.SemErr(bcmd.tok,
                  "Error: break label '" + bcmd.Label + "' must designate an enclosing statement");
              }

              found = true; // don't look any further, since we've found a matching label
              break;
            }
          }

          if (!found)
          {
            if (bcmd.Label == null)
            {
              this.errorHandler.SemErr(bcmd.tok, "Error: break statement is not inside a loop");
            }
            else
            {
              this.errorHandler.SemErr(bcmd.tok,
                "Error: break label '" + bcmd.Label + "' must designate an enclosing statement");
            }
          }
        }

        // recurse
        else if (b.ec is WhileCmd)
        {
          WhileCmd wcmd = (WhileCmd) b.ec;
          CheckLegalLabels(wcmd.Body, stmtList, b);
        }
        else
        {
          for (IfCmd ifcmd = b.ec as IfCmd; ifcmd != null; ifcmd = ifcmd.elseIf)
          {
            CheckLegalLabels(ifcmd.thn, stmtList, b);
            if (ifcmd.elseBlock != null)
            {
              CheckLegalLabels(ifcmd.elseBlock, stmtList, b);
            }
          }
        }
      }
    }

    void NameAnonymousBlocks(StmtList stmtList)
    {
      Contract.Requires(stmtList != null);
      foreach (BigBlock b in stmtList.BigBlocks)
      {
        if (b.LabelName == null)
        {
          b.LabelName = prefix + FreshAnon();
        }

        if (b.ec is WhileCmd)
        {
          WhileCmd wcmd = (WhileCmd) b.ec;
          NameAnonymousBlocks(wcmd.Body);
        }
        else
        {
          for (IfCmd ifcmd = b.ec as IfCmd; ifcmd != null; ifcmd = ifcmd.elseIf)
          {
            NameAnonymousBlocks(ifcmd.thn);
            if (ifcmd.elseBlock != null)
            {
              NameAnonymousBlocks(ifcmd.elseBlock);
            }
          }
        }
      }
    }

    void RecordSuccessors(StmtList stmtList, BigBlock successor)
    {
      Contract.Requires(stmtList != null);
      for (int i = stmtList.BigBlocks.Count; 0 <= --i;)
      {
        BigBlock big = stmtList.BigBlocks[i];
        big.successorBigBlock = successor;

        if (big.ec is WhileCmd)
        {
          WhileCmd wcmd = (WhileCmd) big.ec;
          RecordSuccessors(wcmd.Body, big);
        }
        else
        {
          for (IfCmd ifcmd = big.ec as IfCmd; ifcmd != null; ifcmd = ifcmd.elseIf)
          {
            RecordSuccessors(ifcmd.thn, successor);
            if (ifcmd.elseBlock != null)
            {
              RecordSuccessors(ifcmd.elseBlock, successor);
            }
          }
        }

        successor = big;
      }
    }

    // If the enclosing context is a loop, then "runOffTheEndLabel" is the loop head label;
    // otherwise, it is null.
    void CreateBlocks(StmtList stmtList, string runOffTheEndLabel)
    {
      Contract.Requires(stmtList != null);
      Contract.Requires(blocks != null);
      List<Cmd> cmdPrefixToApply = stmtList.PrefixCommands;

      int n = stmtList.BigBlocks.Count;
      foreach (BigBlock b in stmtList.BigBlocks)
      {
        n--;
        Contract.Assert(b.LabelName != null);
        List<Cmd> theSimpleCmds;
        if (cmdPrefixToApply == null)
        {
          theSimpleCmds = b.simpleCmds;
        }
        else
        {
          theSimpleCmds = new List<Cmd>();
          theSimpleCmds.AddRange(cmdPrefixToApply);
          theSimpleCmds.AddRange(b.simpleCmds);
          cmdPrefixToApply = null; // now, we've used 'em up
        }

        if (b.tc != null)
        {
          // this BigBlock has the very same components as a Block
          Contract.Assert(b.ec == null);
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, b.tc);
          blocks.Add(block);
        }
        else if (b.ec == null)
        {
          TransferCmd trCmd;
          if (n == 0 && runOffTheEndLabel != null)
          {
            // goto the given label instead of the textual successor block
            trCmd = new GotoCmd(stmtList.EndCurly, new List<String> {runOffTheEndLabel});
          }
          else
          {
            trCmd = GotoSuccessor(stmtList.EndCurly, b);
          }

          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, trCmd);
          blocks.Add(block);
        }
        else if (b.ec is BreakCmd)
        {
          BreakCmd bcmd = (BreakCmd) b.ec;
          Contract.Assert(bcmd.BreakEnclosure != null);
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds, GotoSuccessor(b.ec.tok, bcmd.BreakEnclosure));
          blocks.Add(block);
        }
        else if (b.ec is WhileCmd)
        {
          WhileCmd wcmd = (WhileCmd) b.ec;
          var a = FreshAnon();
          string loopHeadLabel = prefix + a + "_LoopHead";
          string /*!*/
            loopBodyLabel = prefix + a + "_LoopBody";
          string loopDoneLabel = prefix + a + "_LoopDone";

          List<Cmd> ssBody = new List<Cmd>();
          List<Cmd> ssDone = new List<Cmd>();
          if (wcmd.Guard != null)
          {
            var ac = new AssumeCmd(wcmd.tok, wcmd.Guard);
            ac.Attributes = new QKeyValue(wcmd.tok, "partition", new List<object>(), null);
            ssBody.Add(ac);

            ac = new AssumeCmd(wcmd.tok, Expr.Not(wcmd.Guard));
            ac.Attributes = new QKeyValue(wcmd.tok, "partition", new List<object>(), null);
            ssDone.Add(ac);
          }

          // Try to squeeze in ssBody into the first block of wcmd.Body
          bool bodyGuardTakenCareOf = wcmd.Body.PrefixFirstBlock(ssBody, ref loopBodyLabel);

          // ... goto LoopHead;
          Block block = new Block(b.tok, b.LabelName, theSimpleCmds,
            new GotoCmd(wcmd.tok, new List<String> {loopHeadLabel}));
          blocks.Add(block);

          // LoopHead: assert/assume loop_invariant; goto LoopDone, LoopBody;
          List<Cmd> ssHead = new List<Cmd>();
          foreach (CallCmd yield in wcmd.Yields)
          {
            ssHead.Add(yield);
          }
          foreach (PredicateCmd inv in wcmd.Invariants)
          {
            ssHead.Add(inv);
          }

          block = new Block(wcmd.tok, loopHeadLabel, ssHead,
            new GotoCmd(wcmd.tok, new List<String> {loopDoneLabel, loopBodyLabel}));
          blocks.Add(block);

          if (!bodyGuardTakenCareOf)
          {
            // LoopBody: assume guard; goto firstLoopBlock;
            block = new Block(wcmd.tok, loopBodyLabel, ssBody,
              new GotoCmd(wcmd.tok, new List<String> {wcmd.Body.BigBlocks[0].LabelName}));
            blocks.Add(block);
          }

          // recurse to create the blocks for the loop body
          CreateBlocks(wcmd.Body, loopHeadLabel);

          // LoopDone: assume !guard; goto loopSuccessor;
          TransferCmd trCmd;
          if (n == 0 && runOffTheEndLabel != null)
          {
            // goto the given label instead of the textual successor block
            trCmd = new GotoCmd(wcmd.tok, new List<String> {runOffTheEndLabel});
          }
          else
          {
            trCmd = GotoSuccessor(wcmd.tok, b);
          }

          block = new Block(wcmd.tok, loopDoneLabel, ssDone, trCmd);
          blocks.Add(block);
        }
        else
        {
          IfCmd ifcmd = (IfCmd) b.ec;
          string predLabel = b.LabelName;
          List<Cmd> predCmds = theSimpleCmds;

          for (; ifcmd != null; ifcmd = ifcmd.elseIf)
          {
            var a = FreshAnon();
            string thenLabel = prefix + a + "_Then";
            Contract.Assert(thenLabel != null);
            string elseLabel = prefix + a + "_Else";
            Contract.Assert(elseLabel != null);

            List<Cmd> ssThen = new List<Cmd>();
            List<Cmd> ssElse = new List<Cmd>();
            if (ifcmd.Guard != null)
            {
              var ac = new AssumeCmd(ifcmd.tok, ifcmd.Guard);
              ac.Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null);
              ssThen.Add(ac);

              ac = new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard));
              ac.Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null);
              ssElse.Add(ac);
            }

            // Try to squeeze in ssThen/ssElse into the first block of ifcmd.thn/ifcmd.elseBlock
            bool thenGuardTakenCareOf = ifcmd.thn.PrefixFirstBlock(ssThen, ref thenLabel);
            bool elseGuardTakenCareOf = false;
            if (ifcmd.elseBlock != null)
            {
              elseGuardTakenCareOf = ifcmd.elseBlock.PrefixFirstBlock(ssElse, ref elseLabel);
            }

            // ... goto Then, Else;
            var jumpBlock = new Block(b.tok, predLabel, predCmds,
              new GotoCmd(ifcmd.tok, new List<String> {thenLabel, elseLabel}));
            blocks.Add(jumpBlock);

            if (!thenGuardTakenCareOf)
            {
              // Then: assume guard; goto firstThenBlock;
              var thenJumpBlock = new Block(ifcmd.tok, thenLabel, ssThen,
                new GotoCmd(ifcmd.tok, new List<String> {ifcmd.thn.BigBlocks[0].LabelName}));
              blocks.Add(thenJumpBlock);
            }

            // recurse to create the blocks for the then branch
            CreateBlocks(ifcmd.thn, n == 0 ? runOffTheEndLabel : null);

            if (ifcmd.elseBlock != null)
            {
              Contract.Assert(ifcmd.elseIf == null);
              if (!elseGuardTakenCareOf)
              {
                // Else: assume !guard; goto firstElseBlock;
                var elseJumpBlock = new Block(ifcmd.tok, elseLabel, ssElse,
                  new GotoCmd(ifcmd.tok, new List<String> {ifcmd.elseBlock.BigBlocks[0].LabelName}));
                blocks.Add(elseJumpBlock);
              }

              // recurse to create the blocks for the else branch
              CreateBlocks(ifcmd.elseBlock, n == 0 ? runOffTheEndLabel : null);
            }
            else if (ifcmd.elseIf != null)
            {
              // this is an "else if"
              predLabel = elseLabel;
              predCmds = new List<Cmd>();
              if (ifcmd.Guard != null)
              {
                var ac = new AssumeCmd(ifcmd.tok, Expr.Not(ifcmd.Guard));
                ac.Attributes = new QKeyValue(ifcmd.tok, "partition", new List<object>(), null);
                predCmds.Add(ac);
              }
            }
            else
            {
              // no else alternative is specified, so else branch is just "skip"
              // Else: assume !guard; goto ifSuccessor;
              TransferCmd trCmd;
              if (n == 0 && runOffTheEndLabel != null)
              {
                // goto the given label instead of the textual successor block
                trCmd = new GotoCmd(ifcmd.tok, new List<String> {runOffTheEndLabel});
              }
              else
              {
                trCmd = GotoSuccessor(ifcmd.tok, b);
              }

              var block = new Block(ifcmd.tok, elseLabel, ssElse, trCmd);
              blocks.Add(block);
            }
          }
        }
      }
    }

    TransferCmd GotoSuccessor(IToken tok, BigBlock b)
    {
      Contract.Requires(b != null);
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      if (b.successorBigBlock != null)
      {
        return new GotoCmd(tok, new List<String> {b.successorBigBlock.LabelName});
      }
      else
      {
        return new ReturnCmd(tok);
      }
    }
  }

  [ContractClass(typeof(StructuredCmdContracts))]
  public abstract class StructuredCmd
  {
    private IToken /*!*/
      _tok;

    public IToken /*!*/ tok
    {
      get
      {
        Contract.Ensures(Contract.Result<IToken>() != null);
        return this._tok;
      }
      set
      {
        Contract.Requires(value != null);
        this._tok = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._tok != null);
    }

    public StructuredCmd(IToken tok)
    {
      Contract.Requires(tok != null);
      this._tok = tok;
    }

    public abstract void Emit(TokenTextWriter /*!*/ stream, int level);
  }

  [ContractClassFor(typeof(StructuredCmd))]
  public abstract class StructuredCmdContracts : StructuredCmd
  {
    public override void Emit(TokenTextWriter stream, int level)
    {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }

    public StructuredCmdContracts() : base(null)
    {
    }
  }

  public class IfCmd : StructuredCmd
  {
    public Expr Guard;

    private StmtList /*!*/
      _thn;

    public StmtList /*!*/ thn
    {
      get
      {
        Contract.Ensures(Contract.Result<StmtList>() != null);
        return this._thn;
      }
      set
      {
        Contract.Requires(value != null);
        this._thn = value;
      }
    }

    private IfCmd _elseIf;

    public IfCmd elseIf
    {
      get { return this._elseIf; }
      set
      {
        Contract.Requires(value == null || this.elseBlock == null);
        this._elseIf = value;
      }
    }

    private StmtList _elseBlock;

    public StmtList elseBlock
    {
      get { return this._elseBlock; }
      set
      {
        Contract.Requires(value == null || this.elseIf == null);
        this._elseBlock = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._thn != null);
      Contract.Invariant(this._elseIf == null || this._elseBlock == null);
    }

    public IfCmd(IToken /*!*/ tok, Expr guard, StmtList /*!*/ thn, IfCmd elseIf, StmtList elseBlock)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(thn != null);
      Contract.Requires(elseIf == null || elseBlock == null);
      this.Guard = guard;
      this._thn = thn;
      this._elseIf = elseIf;
      this._elseBlock = elseBlock;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(level, "if (");
      IfCmd /*!*/
        ifcmd = this;
      while (true)
      {
        if (ifcmd.Guard == null)
        {
          stream.Write("*");
        }
        else
        {
          ifcmd.Guard.Emit(stream);
        }

        stream.WriteLine(")");

        stream.WriteLine(level, "{");
        ifcmd.thn.Emit(stream, level + 1);
        stream.WriteLine(level, "}");

        if (ifcmd.elseIf != null)
        {
          stream.Write(level, "else if (");
          ifcmd = ifcmd.elseIf;
          continue;
        }
        else if (ifcmd.elseBlock != null)
        {
          stream.WriteLine(level, "else");
          stream.WriteLine(level, "{");
          ifcmd.elseBlock.Emit(stream, level + 1);
          stream.WriteLine(level, "}");
        }

        break;
      }
    }
  }

  public class WhileCmd : StructuredCmd
  {
    [Peer] public Expr Guard;

    public List<PredicateCmd> Invariants;

    public List<CallCmd> Yields;

    public StmtList Body;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Body != null);
      Contract.Invariant(cce.NonNullElements(Invariants));
    }


    public WhileCmd(IToken tok, [Captured] Expr guard, List<PredicateCmd> invariants, List<CallCmd> yields, StmtList body)
      : base(tok)
    {
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(body != null);
      Contract.Requires(tok != null);
      this.Guard = guard;
      this.Invariants = invariants;
      this.Yields = yields;
      this.Body = body;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(level, "while (");
      if (Guard == null)
      {
        stream.Write("*");
      }
      else
      {
        Guard.Emit(stream);
      }

      stream.WriteLine(")");

      foreach (var yield in Yields)
      {
        stream.Write(level + 1, "invariant");
        yield.Emit(stream, level + 1);
      }
      foreach (var inv in Invariants)
      {
        if (inv is AssumeCmd)
        {
          stream.Write(level + 1, "free invariant ");
        }
        else
        {
          stream.Write(level + 1, "invariant ");
        }

        Cmd.EmitAttributes(stream, inv.Attributes);
        inv.Expr.Emit(stream);
        stream.WriteLine(";");
      }

      stream.WriteLine(level, "{");
      Body.Emit(stream, level + 1);
      stream.WriteLine(level, "}");
    }
  }

  public class BreakCmd : StructuredCmd
  {
    public string Label;
    public BigBlock BreakEnclosure;

    public BreakCmd(IToken tok, string label)
      : base(tok)
    {
      Contract.Requires(tok != null);
      this.Label = label;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      if (Label == null)
      {
        stream.WriteLine(level, "break;");
      }
      else
      {
        stream.WriteLine(level, "break {0};", Label);
      }
    }
  }

  //---------------------------------------------------------------------
  // Block

  //---------------------------------------------------------------------
  // Commands
  [ContractClassFor(typeof(Cmd))]
  public abstract class CmdContracts : Cmd
  {
    public CmdContracts() : base(null)
    {
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
      Contract.Requires(vars != null);
      throw new NotImplementedException();
    }
  }

  public static class ChecksumHelper
  {
    public static void ComputeChecksums(CoreOptions options, Cmd cmd, Implementation impl, ISet<Variable> usedVariables,
      byte[] currentChecksum = null)
    {
      if (options.VerifySnapshots < 2)
      {
        return;
      }

      if (cmd.IrrelevantForChecksumComputation)
      {
        cmd.Checksum = currentChecksum;
        return;
      }

      var assumeCmd = cmd as AssumeCmd;
      if (assumeCmd != null
          && QKeyValue.FindBoolAttribute(assumeCmd.Attributes, "assumption_variable_initialization"))
      {
        // Ignore assumption variable initializations.
        assumeCmd.Checksum = currentChecksum;
        return;
      }

      using (var strWr = new System.IO.StringWriter())
      using (var tokTxtWr = new TokenTextWriter("<no file>", strWr, false, false, options))
      {
        tokTxtWr.UseForComputingChecksums = true;
        var havocCmd = cmd as HavocCmd;
        if (havocCmd != null)
        {
          tokTxtWr.Write("havoc ");
          var relevantVars = havocCmd.Vars
            .Where(e => usedVariables.Contains(e.Decl) && !e.Decl.Name.StartsWith("a##cached##")).OrderBy(e => e.Name)
            .ToList();
          relevantVars.Emit(tokTxtWr, true);
          tokTxtWr.WriteLine(";");
        }
        else
        {
          cmd.Emit(tokTxtWr, 0);
        }

        var md5 = System.Security.Cryptography.MD5.Create();
        var str = strWr.ToString();
        if (str.Any())
        {
          var data = System.Text.Encoding.UTF8.GetBytes(str);
          var checksum = md5.ComputeHash(data);
          currentChecksum = currentChecksum != null ? CombineChecksums(currentChecksum, checksum) : checksum;
        }

        cmd.Checksum = currentChecksum;
      }

      var assertCmd = cmd as AssertCmd;
      if (assertCmd != null && assertCmd.Checksum != null)
      {
        var assertRequiresCmd = assertCmd as AssertRequiresCmd;
        if (assertRequiresCmd != null)
        {
          impl.AddAssertionChecksum(assertRequiresCmd.Checksum);
          impl.AddAssertionChecksum(assertRequiresCmd.Call.Checksum);
          assertRequiresCmd.SugaredCmdChecksum = assertRequiresCmd.Call.Checksum;
        }
        else
        {
          impl.AddAssertionChecksum(assertCmd.Checksum);
        }
      }

      var sugaredCmd = cmd as SugaredCmd;
      if (sugaredCmd != null)
      {
        // The checksum of a sugared command should not depend on the desugaring itself.
        var stateCmd = sugaredCmd.GetDesugaring(options) as StateCmd;
        if (stateCmd != null)
        {
          foreach (var c in stateCmd.Cmds)
          {
            ComputeChecksums(options, c, impl, usedVariables, currentChecksum);
            currentChecksum = c.Checksum;
            if (c.SugaredCmdChecksum == null)
            {
              c.SugaredCmdChecksum = cmd.Checksum;
            }
          }
        }
        else
        {
          ComputeChecksums(options, sugaredCmd.GetDesugaring(options), impl, usedVariables, currentChecksum);
        }
      }
    }

    public static byte[] CombineChecksums(byte[] first, byte[] second, bool unordered = false)
    {
      Contract.Requires(first != null && (second == null || first.Length == second.Length));

      var result = (byte[]) (first.Clone());
      for (int i = 0; second != null && i < second.Length; i++)
      {
        if (unordered)
        {
          result[i] += second[i];
        }
        else
        {
          result[i] = (byte) (result[i] * 31 ^ second[i]);
        }
      }

      return result;
    }
  }

  /// <summary>
  /// Could have also been called a statement.
  ///
  /// Does not include commands that contain other commands,
  /// for those, look at StructuredCmd
  /// 
  /// </summary>
  [ContractClass(typeof(CmdContracts))]
  public abstract class Cmd : Absy
  {
    public List<int> Layers;
    
    public byte[] Checksum { get; internal set; }
    public byte[] SugaredCmdChecksum { get; internal set; }
    public bool IrrelevantForChecksumComputation { get; set; }

    public Cmd(IToken /*!*/ tok)
      : base(tok)
    {
      Contract.Assert(tok != null);
    }

    public abstract void Emit(TokenTextWriter /*!*/ stream, int level);
    public abstract void AddAssignedVariables(List<Variable> /*!*/ vars);

    public void CheckAssignments(TypecheckingContext tc)
    {
      Contract.Requires(tc != null);
      List<Variable> /*!*/
        vars = new List<Variable>();
      this.AddAssignedVariables(vars);
      foreach (Variable /*!*/ v in vars)
      {
        Contract.Assert(v != null);
        if (!v.IsMutable)
        {
          tc.Error(this, "command assigns to an immutable variable: {0}", v.Name);
        }
        else if (tc.CheckModifies && v is GlobalVariable)
        {
          if (!tc.Yields && !tc.InFrame(v))
          {
            tc.Error(this,
              "command assigns to a global variable that is not in the enclosing {0} modifies clause: {1}",
              tc.Proc is ActionDecl ? "action's" : "procedure's", v.Name);
          }
        }
      }
    }

    // Methods to simulate the old SimpleAssignCmd and MapAssignCmd
    public static AssignCmd SimpleAssign(IToken tok, IdentifierExpr lhs, Expr rhs)
    {
      Contract.Requires(rhs != null);
      Contract.Requires(lhs != null);
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<AssignCmd>() != null);
      List<AssignLhs /*!*/> /*!*/
        lhss = new List<AssignLhs /*!*/>();
      List<Expr /*!*/> /*!*/
        rhss = new List<Expr /*!*/>();

      lhss.Add(new SimpleAssignLhs(lhs.tok, lhs));
      rhss.Add(rhs);

      return new AssignCmd(tok, lhss, rhss);
    }

    public static AssignCmd /*!*/ MapAssign(IToken tok,
      IdentifierExpr /*!*/ map,
      List<Expr> /*!*/ indexes, Expr /*!*/ rhs)
    {
      Contract.Requires(tok != null);
      Contract.Requires(map != null);
      Contract.Requires(indexes != null);
      Contract.Requires(rhs != null);
      Contract.Ensures(Contract.Result<AssignCmd>() != null);
      List<AssignLhs /*!*/> /*!*/
        lhss = new List<AssignLhs /*!*/>();
      List<Expr /*!*/> /*!*/
        rhss = new List<Expr /*!*/>();
      List<Expr /*!*/> /*!*/
        indexesList = new List<Expr /*!*/>();


      foreach (Expr e in indexes)
      {
        indexesList.Add(cce.NonNull(e));
      }

      lhss.Add(new MapAssignLhs(map.tok,
        new SimpleAssignLhs(map.tok, map),
        indexesList));
      rhss.Add(rhs);

      return new AssignCmd(tok, lhss, rhss);
    }

    public static AssignCmd /*!*/ MapAssign(IToken tok,
      IdentifierExpr /*!*/ map,
      params Expr[] /*!*/ args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(map != null);
      Contract.Requires(args != null);
      Contract.Requires(args.Length > 0); // at least the rhs
      Contract.Requires(Contract.ForAll(args, i => i != null));
      Contract.Ensures(Contract.Result<AssignCmd>() != null);

      List<AssignLhs /*!*/> /*!*/
        lhss = new List<AssignLhs /*!*/>();
      List<Expr /*!*/> /*!*/
        rhss = new List<Expr /*!*/>();
      List<Expr /*!*/> /*!*/
        indexesList = new List<Expr /*!*/>();

      for (int i = 0; i < args.Length - 1; ++i)
      {
        indexesList.Add(cce.NonNull(args[i]));
      }

      lhss.Add(new MapAssignLhs(map.tok,
        new SimpleAssignLhs(map.tok, map),
        indexesList));
      rhss.Add(cce.NonNull(args[args.Length - 1]));

      return new AssignCmd(tok, lhss, rhss);
    }

    /// <summary>
    /// This is a helper routine for printing a linked list of attributes.  Each attribute
    /// is terminated by a space.
    /// </summary>
    public static void EmitAttributes(TokenTextWriter stream, QKeyValue attributes)
    {
      Contract.Requires(stream != null);

      if (stream.UseForComputingChecksums)
      {
        return;
      }

      for (QKeyValue kv = attributes; kv != null; kv = kv.Next)
      {
        kv.Emit(stream);
        stream.Write(" ");
      }
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      System.IO.StringWriter buffer = new System.IO.StringWriter();
      using TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false, false, PrintOptions.Default);
      this.Emit(stream, 0);

      return buffer.ToString();
    }
  }
  
  public class CommentCmd : Cmd // just a convenience for debugging
  {
    public readonly string /*!*/
      Comment;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Comment != null);
    }

    public CommentCmd(string c)
      : base(Token.NoToken)
    {
      Contract.Requires(c != null);
      Comment = c;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      if (stream.UseForComputingChecksums)
      {
        return;
      }

      if (this.Comment.Contains("\n"))
      {
        stream.WriteLine(this, level, "/* {0} */", this.Comment);
      }
      else
      {
        stream.WriteLine(this, level, "// {0}", this.Comment);
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
    }

    public override void Typecheck(TypecheckingContext tc)
    {
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitCommentCmd(this);
    }
  }

  // class for parallel assignments, which subsumes both the old
  // SimpleAssignCmd and the old MapAssignCmd
  public class AssignCmd : Cmd, ICarriesAttributes
  {
    public QKeyValue Attributes { get; set; }

    private List<AssignLhs> _lhss;

    public IList<AssignLhs> Lhss
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IList<AssignLhs>>()));
        Contract.Ensures(Contract.Result<IList<AssignLhs>>().IsReadOnly);
        return this._lhss.AsReadOnly();
      }
      set
      {
        Contract.Requires(cce.NonNullElements(value));
        this._lhss = new List<AssignLhs>(value);
      }
    }

    internal void SetLhs(int index, AssignLhs lhs)
    {
      Contract.Requires(0 <= index && index < this.Lhss.Count);
      Contract.Requires(lhs != null);
      Contract.Ensures(this.Lhss[index] == lhs);
      this._lhss[index] = lhs;
    }

    private List<Expr> _rhss;

    public IList<Expr> Rhss
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IList<Expr>>()));
        Contract.Ensures(Contract.Result<IList<Expr>>().IsReadOnly);
        return this._rhss.AsReadOnly();
      }
      set
      {
        Contract.Requires(cce.NonNullElements(value));
        this._rhss = new List<Expr>(value);
      }
    }

    internal void SetRhs(int index, Expr rhs)
    {
      Contract.Requires(0 <= index && index < this.Rhss.Count);
      Contract.Requires(rhs != null);
      Contract.Ensures(this.Rhss[index] == rhs);
      this._rhss[index] = rhs;
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullElements(this._lhss));
      Contract.Invariant(cce.NonNullElements(this._rhss));
    }

    public AssignCmd(IToken tok, IList<AssignLhs> lhss, IList<Expr> rhss, QKeyValue kv)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(cce.NonNullElements(lhss));
      this._lhss = new List<AssignLhs>(lhss);
      this._rhss = new List<Expr>(rhss);
      this.Attributes = kv;
    }

    public AssignCmd(IToken tok, IList<AssignLhs> lhss, IList<Expr> rhss)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(cce.NonNullElements(lhss));
      this._lhss = new List<AssignLhs>(lhss);
      this._rhss = new List<Expr>(rhss);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "");

      string /*!*/
        sep = "";
      foreach (AssignLhs /*!*/ l in Lhss)
      {
        Contract.Assert(l != null);
        stream.Write(sep);
        sep = ", ";
        l.Emit(stream);
      }

      stream.Write(" := ");

      sep = "";
      foreach (Expr /*!*/ e in Rhss)
      {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }

      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      (this as ICarriesAttributes).ResolveAttributes(rc);
      if (Lhss.Count != Rhss.Count)
      {
        rc.Error(this,
          "number of left-hand sides does not match number of right-hand sides");
      }

      foreach (AssignLhs /*!*/ e in Lhss)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }

      foreach (Expr /*!*/ e in Rhss)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }

      // check for double occurrences of assigned variables
      // (could be optimised)
      for (int i = 0; i < Lhss.Count; ++i)
      {
        for (int j = i + 1; j < Lhss.Count; ++j)
        {
          if (cce.NonNull(Lhss[i].DeepAssignedVariable).Equals(
            Lhss[j].DeepAssignedVariable))
          {
            rc.Error(Lhss[j],
              "variable {0} is assigned more than once in parallel assignment",
              Lhss[j].DeepAssignedVariable);
          }
        }
      }

      for (int i = 0; i < Lhss.Count; i++)
      {
        var lhs = Lhss[i] as SimpleAssignLhs;
        if (lhs == null)
        {
          continue;
        }
        var decl = lhs.AssignedVariable.Decl;
        if (lhs.AssignedVariable.Decl != null && QKeyValue.FindBoolAttribute(decl.Attributes, "assumption"))
        {
          var rhs = Rhss[i] as NAryExpr;
          if (rhs == null
              || !(rhs.Fun is BinaryOperator)
              || ((BinaryOperator)rhs.Fun).Op != BinaryOperator.Opcode.And
              || !(rhs.Args[0] is IdentifierExpr)
              || ((IdentifierExpr)rhs.Args[0]).Decl != decl)
          {
            rc.Error(tok,
              string.Format(
                "RHS of assignment to assumption variable {0} must match expression \"{0} && <boolean expression>\"",
                decl.Name));
          }
          else if (rc.HasVariableBeenAssigned(decl.Name))
          {
            rc.Error(tok, "assumption variable may not be assigned to more than once");
          }
          else
          {
            rc.MarkVariableAsAssigned(decl.Name);
          }
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      int errorCount = tc.ErrorCount;

      (this as ICarriesAttributes).TypecheckAttributes(tc);

      var expectedLayerRanges = new List<LayerRange>();
      if (tc.Proc is YieldProcedureDecl)
      {
        foreach (var e in Lhss.Where(e => e.DeepAssignedVariable is GlobalVariable))
        {
          tc.Error(e, $"global variable directly modified in a yield procedure: {e.DeepAssignedVariable.Name}");
        }
        expectedLayerRanges = Lhss.Select(e => e.DeepAssignedVariable.LayerRange).ToList();
      }

      foreach (AssignLhs /*!*/ e in Lhss)
      {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }

      for (int i = 0; i < Rhss.Count; i++)
      {
        var e = Rhss[i];
        Contract.Assert(e != null);
        tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl;
        tc.ExpectedLayerRange = tc.Proc is YieldProcedureDecl ? expectedLayerRanges[i] : null;
        e.Typecheck(tc);
        tc.GlobalAccessOnlyInOld = false;
        tc.ExpectedLayerRange = null;
      }

      if (tc.ErrorCount > errorCount)
      {
        // there has already been an error when typechecking the lhs or rhs
        return;
      }

      this.CheckAssignments(tc);

      for (int i = 0; i < Lhss.Count; ++i)
      {
        Type ltype = Lhss[i].Type;
        Type rtype = Rhss[i].Type;
        if (!ltype.Unify(rtype))
        {
          tc.Error(Lhss[i], "mismatched types in assignment command (cannot assign {0} to {1})", rtype, ltype);
        }
      }
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
      foreach (AssignLhs /*!*/ l in Lhss)
      {
        Contract.Assert(l != null);
        vars.Add(l.DeepAssignedVariable);
      }
    }

    // transform away the syntactic sugar of map assignments and
    // determine an equivalent assignment in which all rhs are simple
    // variables
    public AssignCmd /*!*/ AsSimpleAssignCmd
    {
      get
      {
        Contract.Ensures(Contract.Result<AssignCmd>() != null);

        List<AssignLhs /*!*/> /*!*/
          newLhss = new List<AssignLhs /*!*/>();
        List<Expr /*!*/> /*!*/
          newRhss = new List<Expr /*!*/>();

        for (int i = 0; i < Lhss.Count; ++i)
        {
          Lhss[i].AsSimpleAssignment(Rhss[i], out var newLhs, out var newRhs);
          newLhss.Add(new SimpleAssignLhs(Token.NoToken, newLhs));
          newRhss.Add(newRhs);
        }

        return new AssignCmd(Token.NoToken, newLhss, newRhss, Attributes);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitAssignCmd(this);
    }
  }

  // There are two different kinds of left-hand sides in assignments:
  // simple variables (identifiers), or locations of a map
  [ContractClass(typeof(AssignLhsContracts))]
  public abstract class AssignLhs : Absy
  {
    // The type of the lhs is determined during typechecking
    public abstract Type Type { get; }

    // Determine the variable that is actually assigned in this lhs
    public abstract IdentifierExpr /*!*/ DeepAssignedIdentifier { get; }
    public abstract Variable DeepAssignedVariable { get; }

    public AssignLhs(IToken /*!*/ tok)
      : base(tok)
    {
      Contract.Requires(tok != null);
    }

    public abstract void Emit(TokenTextWriter /*!*/ stream);

    public abstract Expr /*!*/ AsExpr { get; }

    // transform away the syntactic sugar of map assignments and
    // determine an equivalent simple assignment
    internal abstract void AsSimpleAssignment(Expr /*!*/ rhs,
      out IdentifierExpr /*!*/ simpleLhs,
      out Expr /*!*/ simpleRhs);
  }

  [ContractClassFor(typeof(AssignLhs))]
  public abstract class AssignLhsContracts : AssignLhs
  {
    public AssignLhsContracts() : base(null)
    {
    }

    public override IdentifierExpr DeepAssignedIdentifier
    {
      get
      {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
        throw new NotImplementedException();
      }
    }

    public override Expr AsExpr
    {
      get
      {
        Contract.Ensures(Contract.Result<Expr>() != null);
        throw new NotImplementedException();
      }
    }

    internal override void AsSimpleAssignment(Expr rhs, out IdentifierExpr simpleLhs, out Expr simpleRhs)
    {
      Contract.Requires(rhs != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleLhs) != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleRhs) != null);

      throw new NotImplementedException();
    }
  }

  public class SimpleAssignLhs : AssignLhs
  {
    public IdentifierExpr /*!*/
      AssignedVariable;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(AssignedVariable != null);
    }


    public override Type Type => AssignedVariable.Type.Expanded;

    public override IdentifierExpr /*!*/ DeepAssignedIdentifier
    {
      get
      {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
        return AssignedVariable;
      }
    }

    public override Variable DeepAssignedVariable
    {
      get { return AssignedVariable.Decl; }
    }

    public SimpleAssignLhs(IToken tok, IdentifierExpr assignedVariable)
      : base(tok)
    {
      Contract.Requires(assignedVariable != null);
      Contract.Requires(tok != null);
      AssignedVariable = assignedVariable;
    }

    public override void Resolve(ResolutionContext rc)
    {
      AssignedVariable.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      AssignedVariable.Typecheck(tc);
    }

    public override void Emit(TokenTextWriter stream)
    {
      AssignedVariable.Emit(stream);
    }

    public override Expr /*!*/ AsExpr
    {
      get
      {
        Contract.Ensures(Contract.Result<Expr>() != null);

        return AssignedVariable;
      }
    }

    internal override void AsSimpleAssignment(Expr rhs,
      out IdentifierExpr /*!*/ simpleLhs,
      out Expr /*!*/ simpleRhs)
    {
      simpleLhs = AssignedVariable;
      simpleRhs = rhs;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitSimpleAssignLhs(this);
    }
  }

  // A map-assignment-lhs (m[t1, t2, ...] := ...) is quite similar to
  // a map select expression, but it is cleaner to keep those two
  // things separate
  public class MapAssignLhs : AssignLhs
  {
    public AssignLhs /*!*/
      Map;

    public List<Expr /*!*/> /*!*/
      Indexes;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Map != null);
      Contract.Invariant(cce.NonNullElements(Indexes));
    }


    // The instantiation of type parameters of the map that is
    // determined during type checking.
    public TypeParamInstantiation TypeParameters = null;

    private Type TypeAttr = null;

    public override Type Type
    {
      get
      {
        if (TypeAttr == null)
        {
          TypeAttr = ((MapType)TypeProxy.FollowProxy(Map.Type.Expanded)).Result.Substitute(
            TypeParameters.FormalTypeParams.ToDictionary(x => x, x => TypeParameters[x]));
        }
        return TypeAttr;
      }
    }

    public override IdentifierExpr /*!*/ DeepAssignedIdentifier
    {
      get
      {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);

        return Map.DeepAssignedIdentifier;
      }
    }

    public override Variable DeepAssignedVariable
    {
      get { return Map.DeepAssignedVariable; }
    }

    public MapAssignLhs(IToken tok, AssignLhs map, List<Expr /*!*/> /*!*/ indexes)
      : base(tok)
    {
      Contract.Requires(map != null);
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(indexes));

      Map = map;
      Indexes = indexes;
    }

    public override void Resolve(ResolutionContext rc)
    {
      Map.Resolve(rc);
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      Map.Typecheck(tc);
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }

      // we use the same typechecking code as in MapSelect
      List<Expr> /*!*/
        selectArgs = new List<Expr>();
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        selectArgs.Add(e);
      }

      TypeAttr =
        MapSelect.Typecheck(cce.NonNull(Map.Type), Map,
          selectArgs, out var tpInsts, tc, tok, "map assignment");
      TypeParameters = tpInsts;
    }

    public override void Emit(TokenTextWriter stream)
    {
      Map.Emit(stream);
      stream.Write("[");
      string /*!*/
        sep = "";
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }

      stream.Write("]");
    }

    public override Expr /*!*/ AsExpr
    {
      get
      {
        Contract.Ensures(Contract.Result<Expr>() != null);

        NAryExpr /*!*/
          res = Expr.Select(Map.AsExpr, Indexes);
        Contract.Assert(res != null);
        res.TypeParameters = this.TypeParameters;
        res.Type = this.Type;
        return res;
      }
    }

    internal override void AsSimpleAssignment(Expr rhs,
      out IdentifierExpr /*!*/ simpleLhs,
      out Expr /*!*/ simpleRhs)
    {
      //Contract.Requires(rhs != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleLhs) != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleRhs) != null);

      NAryExpr /*!*/
        newRhs = Expr.Store(Map.AsExpr, Indexes, rhs);
      Contract.Assert(newRhs != null);
      newRhs.TypeParameters = this.TypeParameters;
      newRhs.Type = Map.Type;
      Map.AsSimpleAssignment(newRhs, out simpleLhs, out simpleRhs);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitMapAssignLhs(this);
    }
  }

  public class FieldAssignLhs : AssignLhs
  {
    public AssignLhs Datatype;

    public FieldAccess FieldAccess;

    public TypeParamInstantiation TypeParameters = null;

    private Type TypeAttr = null;

    public override Type Type
    {
      get
      {
        if (TypeAttr == null)
        {
          TypeAttr = FieldAccess.Type((CtorType)TypeProxy.FollowProxy(Datatype.Type.Expanded));
        }
        return TypeAttr;
      }
    }

    public override IdentifierExpr DeepAssignedIdentifier => Datatype.DeepAssignedIdentifier;

    public override Variable DeepAssignedVariable => Datatype.DeepAssignedVariable;

    public FieldAssignLhs(IToken tok, AssignLhs datatype, FieldAccess fieldAccess)
      : base(tok)
    {
      Datatype = datatype;
      this.FieldAccess = fieldAccess;
    }

    public override void Resolve(ResolutionContext rc)
    {
      Datatype.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      var errorCount = tc.ErrorCount;
      Datatype.Typecheck(tc);
      TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      if (tc.ErrorCount == errorCount)
      {
        TypeAttr = FieldAccess.Typecheck(Datatype.Type, tc, out TypeParameters);
      }
    }

    public override void Emit(TokenTextWriter stream)
    {
      Datatype.Emit(stream);
      stream.Write("->{0}", FieldAccess.FieldName);
    }

    public override Expr AsExpr
    {
      get
      {
        var res = FieldAccess.Select(tok, Datatype.AsExpr);
        Contract.Assert(res != null);
        res.TypeParameters = this.TypeParameters;
        res.Type = this.Type;
        return res;
      }
    }

    internal override void AsSimpleAssignment(Expr rhs,
      out IdentifierExpr simpleLhs,
      out Expr simpleRhs)
    {
      var newRhs = FieldAccess.Update(tok, Datatype.AsExpr, rhs);
      Contract.Assert(newRhs != null);
      newRhs.TypeParameters = this.TypeParameters;
      newRhs.Type = Datatype.Type;
      Datatype.AsSimpleAssignment(newRhs, out simpleLhs, out simpleRhs);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitFieldAssignLhs(this);
    }
  }

  /// <summary>
  /// UnpackCmd used for unpacking a constructed value into its components.
  /// </summary>
  public class UnpackCmd : SugaredCmd, ICarriesAttributes
  {
    private NAryExpr lhs;
    private Expr rhs;
    private QKeyValue kv;

    public UnpackCmd(IToken tok, NAryExpr lhs, Expr rhs, QKeyValue kv)
    : base(tok)
    {
      this.lhs = lhs;
      this.rhs = rhs;
      this.kv = kv;
    }

    public QKeyValue Attributes
    {
      get { return kv; }
      set { kv = value; }
    }

    public override void Resolve(ResolutionContext rc)
    {
      lhs.Resolve(rc);
      rhs.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);

      LayerRange expectedLayerRange = null;
      if (tc.Proc is YieldProcedureDecl)
      {
        UnpackedLhs.Select(ie => ie.Decl).ForEach(v =>
        {
          if (v is GlobalVariable)
          {
            tc.Error(v, $"global variable directly modified in a yield procedure: {v.Name}");
          }
        });
        expectedLayerRange = LayerRange.Union(UnpackedLhs.Select(ie => ie.Decl.LayerRange).ToList());
      }

      lhs.Typecheck(tc);
      
      tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl;
      tc.ExpectedLayerRange = expectedLayerRange;
      rhs.Typecheck(tc);
      tc.GlobalAccessOnlyInOld = false;
      tc.ExpectedLayerRange = null;
      
      this.CheckAssignments(tc);
      Type ltype = lhs.Type;
      Type rtype = rhs.Type;
      if (ltype == null || rtype == null)
      {
        return;
      }
      if (!ltype.Unify(rtype))
      {
        tc.Error(tok, "mismatched types in assignment command (cannot assign {0} to {1})", rtype, ltype);
        return;
      }
      var f = (FunctionCall)lhs.Fun;
      if (!(f.Func is DatatypeConstructor))
      {
        tc.Error(tok, "left side of unpack command must be a constructor application");
      }
      var assignedVars = new HashSet<Variable>();
      UnpackedLhs.ForEach(ie =>
      {
        if (assignedVars.Contains(ie.Decl))
        {
          tc.Error(tok, $"variable {ie.Decl} is assigned more than once in unpack command");
        }
        else
        {
          assignedVars.Add(ie.Decl);
        }
      });
    }

    public DatatypeConstructor Constructor => (DatatypeConstructor)((FunctionCall)lhs.Fun).Func;

    public NAryExpr Lhs
    {
      get
      {
        return lhs;
      }
      set
      {
        lhs = value;
      }
    }

    public Expr Rhs
    {
      get
      {
        return rhs;
      }
      set
      {
        rhs = value;
      }
    }

    public IEnumerable<IdentifierExpr> UnpackedLhs => lhs.Args.Cast<IdentifierExpr>();

    public override void AddAssignedVariables(List<Variable> vars)
    {
      lhs.Args.Cast<IdentifierExpr>().ForEach(arg => vars.Add(arg.Decl));
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "");
      lhs.Emit(stream);
      stream.Write(" := ");
      rhs.Emit(stream);
      stream.WriteLine(";");
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitUnpackCmd(this);
    }

    protected override Cmd ComputeDesugaring(PrintOptions options)
    {
      var cmds = new List<Cmd>();
      // assert that unpacked value has the correct constructor
      var assertCmd = new AssertCmd(tok,
        new NAryExpr(tok, new IsConstructor(tok, Constructor.datatypeTypeCtorDecl, Constructor.index),
          new List<Expr> { rhs })) { Description = new FailureOnlyDescription("the precondition for unpack could not be proved") };
      cmds.Add(assertCmd);
      // read fields into lhs variables from localRhs
      var assignLhss = lhs.Args.Select(arg => new SimpleAssignLhs(tok, (IdentifierExpr)arg)).ToList<AssignLhs>();
      var assignRhss = Enumerable.Range(0, Constructor.InParams.Count).Select(i =>
      {
        var fieldName = Constructor.InParams[i].Name;
        var fieldAccess = new FieldAccess(tok, fieldName, Constructor.datatypeTypeCtorDecl,
          new List<DatatypeAccessor> { new DatatypeAccessor(Constructor.index, i) });
        return new NAryExpr(tok, fieldAccess, new List<Expr> { rhs });
      }).ToList<Expr>();
      cmds.Add(new AssignCmd(tok, assignLhss, assignRhss));
      return new StateCmd(tok, new List<Variable>(), cmds);
    }
  }

  /// <summary>
  /// A StateCmd is like an imperative-let binding around a sequence of commands.
  /// There is no user syntax for a StateCmd.  Instead, a StateCmd is only used
  /// temporarily during the desugaring phase inside the VC generator.
  /// </summary>
  public class StateCmd : Cmd
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._locals != null);
      Contract.Invariant(this._cmds != null);
    }

    private List<Variable> _locals;

    public /*readonly, except for the StandardVisitor*/ List<Variable> /*!*/ Locals
    {
      get
      {
        Contract.Ensures(Contract.Result<List<Variable>>() != null);
        return this._locals;
      }
      internal set
      {
        Contract.Requires(value != null);
        this._locals = value;
      }
    }

    private List<Cmd> _cmds;

    public /*readonly, except for the StandardVisitor*/ List<Cmd> /*!*/ Cmds
    {
      get
      {
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);
        return this._cmds;
      }
      set
      {
        Contract.Requires(value != null);
        this._cmds = value;
      }
    }

    public StateCmd(IToken tok, List<Variable> /*!*/ locals, List<Cmd> /*!*/ cmds)
      : base(tok)
    {
      Contract.Requires(locals != null);
      Contract.Requires(cmds != null);
      Contract.Requires(tok != null);
      this._locals = locals;
      this._cmds = cmds;
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      rc.PushVarContext();
      foreach (Variable /*!*/ v in Locals)
      {
        Contract.Assert(v != null);
        rc.AddVariable(v);
      }

      foreach (Cmd /*!*/ cmd in Cmds)
      {
        Contract.Assert(cmd != null);
        cmd.Resolve(rc);
      }

      rc.PopVarContext();
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
      //Contract.Requires(vars != null);
      List<Variable> vs = new List<Variable>();
      foreach (Cmd cmd in this.Cmds)
      {
        Contract.Assert(cmd != null);
        cmd.AddAssignedVariables(vs);
      }

      var localsSet = new HashSet<Variable>(this.Locals);
      foreach (Variable v in vs)
      {
        Contract.Assert(v != null);
        if (!localsSet.Contains(v))
        {
          vars.Add(v);
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (Cmd /*!*/ cmd in Cmds)
      {
        Contract.Assert(cmd != null);
        cmd.Typecheck(tc);
      }
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.WriteLine(this, level, "{");
      foreach (Variable /*!*/ v in Locals)
      {
        Contract.Assert(v != null);
        v.Emit(stream, level + 1);
      }

      foreach (Cmd /*!*/ c in Cmds)
      {
        Contract.Assert(c != null);
        c.Emit(stream, level + 1);
      }

      stream.WriteLine(level, "}");
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitStateCmd(this);
    }
  }

  [ContractClass(typeof(SugaredCmdContracts))]
  public abstract class SugaredCmd : Cmd
  {
    private Cmd desugaring; // null until desugared

    public SugaredCmd(IToken tok)
      : base(tok)
    {
      Contract.Requires(tok != null);
    }

    public Cmd GetDesugaring(PrintOptions options)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);

      if (desugaring == null) {
        desugaring = ComputeDesugaring(options);
      }

      return desugaring;
    }

    public void ResetDesugaring()
    {
      desugaring = null;
    }
    
    /// <summary>
    /// This method invokes "visitor.Visit" on the desugaring, and then updates the
    /// desugaring to the result thereof.  The method's intended use is for subclasses
    /// of StandardVisitor that need to also visit the desugaring.  Note, since the
    /// "desugaring" field is updated, this is not an appropriate method to be called
    /// by a ReadOnlyVisitor; such visitors should instead just call
    /// visitor.Visit(sugaredCmd.Desugaring).
    /// </summary>
    public void VisitDesugaring(StandardVisitor visitor)
    {
      Contract.Requires(visitor != null && !(visitor is ReadOnlyVisitor));
      if (desugaring != null)
      {
        desugaring = (Cmd) visitor.Visit(desugaring);
      }
    }

    protected abstract Cmd /*!*/ ComputeDesugaring(PrintOptions options);

    public void ExtendDesugaring(CoreOptions options, IEnumerable<Cmd> before, IEnumerable<Cmd> beforePreconditionCheck,
      IEnumerable<Cmd> after)
    {
      var desug = GetDesugaring(options);
      var stCmd = desug as StateCmd;
      if (stCmd != null)
      {
        stCmd.Cmds.InsertRange(0, before);
        var idx = stCmd.Cmds.FindIndex(c => c is AssertCmd || c is HavocCmd || c is AssumeCmd);
        if (idx < 0)
        {
          idx = 0;
        }

        stCmd.Cmds.InsertRange(idx, beforePreconditionCheck);
        stCmd.Cmds.AddRange(after);
      }
      else if (desug != null)
      {
        var cmds = new List<Cmd>(before);
        cmds.Add(desug);
        cmds.AddRange(after);
        desugaring = new StateCmd(Token.NoToken, new List<Variable>(), cmds);
      }
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      if (stream.Options.PrintDesugarings && !stream.UseForComputingChecksums)
      {
        stream.WriteLine(this, level, "/*** desugaring:");
        GetDesugaring(stream.Options).Emit(stream, level);
        stream.WriteLine(level, "**** end desugaring */");
      }
    }
  }

  [ContractClassFor(typeof(SugaredCmd))]
  public abstract class SugaredCmdContracts : SugaredCmd
  {
    public SugaredCmdContracts() : base(null)
    {
    }

    protected override Cmd ComputeDesugaring(PrintOptions options)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);

      throw new NotImplementedException();
    }
  }

  public abstract class CallCommonality : SugaredCmd, ICarriesAttributes
  {
    public QKeyValue Attributes { get; set; }

    private bool isFree = false;

    public bool IsFree
    {
      get { return isFree; }
      set { isFree = value; }
    }

    private bool isAsync = false;

    public bool IsAsync
    {
      get { return isAsync; }
      set { isAsync = value; }
    }

    protected CallCommonality(IToken tok, QKeyValue kv)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Attributes = kv;
    }

    protected enum TempVarKind
    {
      Formal,
      Old,
      Bound
    }

    // We have to give the type explicitly, because the type of the formal "likeThisOne" can contain type variables
    protected Variable CreateTemporaryVariable(List<Variable> tempVars, Variable likeThisOne, Type ty, TempVarKind kind,
      ref int uniqueId)
    {
      Contract.Requires(ty != null);
      Contract.Requires(likeThisOne != null);
      Contract.Requires(tempVars != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      string /*!*/
        tempNamePrefix;
      switch (kind)
      {
        case TempVarKind.Formal:
          tempNamePrefix = "formal@";
          break;
        case TempVarKind.Old:
          tempNamePrefix = "old@";
          break;
        case TempVarKind.Bound:
          tempNamePrefix = "forall@";
          break;
        default:
        {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        } // unexpected kind
      }

      TypedIdent ti = likeThisOne.TypedIdent;
      int id = uniqueId++;
      TypedIdent newTi = new TypedIdent(ti.tok, "call" + id + tempNamePrefix + ti.Name, ty);
      Variable v;
      if (kind == TempVarKind.Bound)
      {
        v = new BoundVariable(likeThisOne.tok, newTi);
      }
      else
      {
        v = new LocalVariable(likeThisOne.tok, newTi);
        tempVars.Add(v);
      }
      return v;
    }
  }

  public class ParCallCmd : CallCommonality
  {
    public List<CallCmd> CallCmds;

    public ParCallCmd(IToken tok, List<CallCmd> callCmds)
      : base(tok, null)
    {
      this.CallCmds = callCmds;
    }

    public ParCallCmd(IToken tok, List<CallCmd> callCmds, QKeyValue kv)
      : base(tok, kv)
    {
      this.CallCmds = callCmds;
    }

    protected override Cmd ComputeDesugaring(PrintOptions options)
    {
      throw new NotImplementedException();
    }

    public ProofObligationDescription Description { get; set; } = new PreconditionDescription();

    public override void Resolve(ResolutionContext rc)
    {
      (this as ICarriesAttributes).ResolveAttributes(rc);
      foreach (CallCmd callCmd in CallCmds)
      {
        callCmd.Resolve(rc);
      }

      HashSet<Variable> parallelCallLhss = new HashSet<Variable>();
      Dictionary<Variable, List<CallCmd>> inputVariables = new Dictionary<Variable, List<CallCmd>>();
      CallCmds.ForEach(c =>
      {
        foreach (var v in VariableCollector.Collect(c.Ins))
        {
          if (!inputVariables.ContainsKey(v))
          {
            inputVariables[v] = new List<CallCmd>();
          }

          inputVariables[v].Add(c);
        }
      });
      foreach (CallCmd callCmd in CallCmds)
      {
        foreach (IdentifierExpr ie in callCmd.Outs)
        {
          if (parallelCallLhss.Contains(ie.Decl))
          {
            rc.Error(this, "left-hand side of parallel call command contains variable twice: {0}", ie.Name);
          }
          else if (inputVariables.ContainsKey(ie.Decl) &&
                   (inputVariables[ie.Decl].Count > 1 || inputVariables[ie.Decl][0] != callCmd))
          {
            rc.Error(this,
              "left-hand side of parallel call command contains variable accessed on the right-hand side of a different arm: {0}",
              ie.Name);
          }
          else
          {
            parallelCallLhss.Add(ie.Decl);
          }
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);
      if (tc.CheckModifies)
      {
        if (!tc.Yields)
        {
          tc.Error(this, "calling procedure of a parallel call must yield");
        }

        foreach (CallCmd callCmd in CallCmds)
        {
          if (callCmd.Proc is YieldProcedureDecl || callCmd.Proc is YieldInvariantDecl)
          {
            continue;
          }
          tc.Error(callCmd, "target procedure of a parallel call must yield");
        }
      }
      foreach (CallCmd callCmd in CallCmds)
      {
        callCmd.Typecheck(tc);
      }

      var markedCallCount = CallCmds.Count(CivlAttributes.IsCallMarked);
      if (markedCallCount > 0)
      {
        if (markedCallCount > 1)
        {
          tc.Error(this, "at most one arm of a parallel call may be annotated with :mark");
        }
        var callerDecl = (YieldProcedureDecl)tc.Proc;
        CallCmds.ForEach(callCmd =>
        {
          if (!CivlAttributes.IsCallMarked(callCmd) && callCmd.Proc is YieldProcedureDecl calleeDecl &&
              callerDecl.Layer == calleeDecl.Layer)
          {
            callCmd.Outs.Where(ie => callerDecl.VisibleFormals.Contains(ie.Decl)).ForEach(ie =>
              {
                tc.Error(ie, $"unmarked call modifies visible output variable of the caller: {ie.Decl}");
              });
          }
        });
      }
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
      foreach (CallCmd callCmd in CallCmds)
      {
        callCmd.AddAssignedVariables(vars);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitParCallCmd(this);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "");
      stream.Write("par ");
      EmitAttributes(stream, Attributes);
      string sep = "";
      bool first = true;
      foreach (var callCmd in CallCmds)
      {
        if (!first)
        {
          stream.Write(" | ");
        }

        first = false;
        if (callCmd.Outs.Count > 0)
        {
          foreach (Expr arg in callCmd.Outs)
          {
            stream.Write(sep);
            sep = ", ";
            if (arg == null)
            {
              stream.Write("*");
            }
            else
            {
              arg.Emit(stream);
            }
          }

          stream.Write(" := ");
        }

        stream.Write(TokenTextWriter.SanitizeIdentifier(callCmd.callee));
        stream.Write("(");
        sep = "";
        foreach (Expr arg in callCmd.Ins)
        {
          stream.Write(sep);
          sep = ", ";
          if (arg == null)
          {
            stream.Write("*");
          }
          else
          {
            arg.Emit(stream);
          }
        }

        stream.Write(")");
      }

      stream.WriteLine(";");
      base.Emit(stream, level);
    }
  }

  public abstract class PredicateCmd : Cmd, ICarriesAttributes
  {
    public QKeyValue Attributes { get; set; }

    public /*readonly--except in StandardVisitor*/ Expr /*!*/
      Expr;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Expr != null);
    }

    public PredicateCmd(IToken /*!*/ tok, Expr /*!*/ expr)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
    }

    public PredicateCmd(IToken /*!*/ tok, Expr /*!*/ expr, QKeyValue kv)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
      Attributes = kv;
    }

    public override void Resolve(ResolutionContext rc)
    {
      Expr.Resolve(rc);
      (this as ICarriesAttributes).ResolveAttributes(rc);
      Layers = (this as ICarriesAttributes).FindLayers();
      if (rc.Proc is YieldProcedureDecl yieldProcedureDecl && this is AssertCmd && !this.HasAttribute(CivlAttributes.YIELDS))
      {
        if (Layers.Count == 0)
        {
          rc.Error(this, "expected layers");
        }
        else if (Layers[^1] > yieldProcedureDecl.Layer)
        {
          rc.Error(this, $"each layer must not be more than {yieldProcedureDecl.Layer}");
        }
      }
      var id = QKeyValue.FindStringAttribute(Attributes, "id");
      if (id != null)
      {
        rc.AddStatementId(tok, id);
      }
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
    }
  }

  public abstract class MiningStrategy
  {
    // abstract class to bind all types of enhanced error data types together
  }

  public class ListOfMiningStrategies : MiningStrategy
  {
    private List<MiningStrategy> /*!*/
      _msList;

    public List<MiningStrategy> /*!*/ msList
    {
      get
      {
        Contract.Ensures(Contract.Result<List<MiningStrategy>>() != null);
        return this._msList;
      }
      set
      {
        Contract.Requires(value != null);
        this._msList = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._msList != null);
    }

    public ListOfMiningStrategies(List<MiningStrategy> l)
    {
      Contract.Requires(l != null);
      this._msList = l;
    }
  }

  public class EEDTemplate : MiningStrategy
  {
    private string /*!*/
      _reason;

    public string /*!*/ reason
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._reason;
      }
      set
      {
        Contract.Requires(value != null);
        this._reason = value;
      }
    }

    private List<Expr /*!*/> /*!*/
      exprList;

    public IEnumerable<Expr> Expressions
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expr>>()));
        return this.exprList.AsReadOnly();
      }
      set
      {
        Contract.Requires(cce.NonNullElements(value));
        this.exprList = new List<Expr>(value);
      }
    }


    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._reason != null);
      Contract.Invariant(cce.NonNullElements(this.exprList));
    }

    public EEDTemplate(string reason, List<Expr /*!*/> /*!*/ exprList)
    {
      Contract.Requires(reason != null);
      Contract.Requires(cce.NonNullElements(exprList));
      this._reason = reason;
      this.exprList = exprList;
    }
  }

  public class AssertCmd : PredicateCmd
  {
    public Expr OrigExpr;
    public Dictionary<Variable, Expr> IncarnationMap;

    Expr verifiedUnder;

    public Expr VerifiedUnder
    {
      get
      {
        if (verifiedUnder != null)
        {
          return verifiedUnder;
        }
        verifiedUnder = QKeyValue.FindExprAttribute(Attributes, "verified_under");
        return verifiedUnder;
      }
    }

    public void MarkAsVerifiedUnder(Expr expr)
    {
      Attributes = new QKeyValue(tok, "verified_under", new List<object> {expr}, Attributes);
      verifiedUnder = expr;
    }

    public ProofObligationDescription Description { get; set; }

    public string ErrorMessage
    {
      get { return QKeyValue.FindStringAttribute(Attributes, "msg"); }
    }

    private MiningStrategy errorDataEnhanced;

    public MiningStrategy ErrorDataEnhanced
    {
      get { return errorDataEnhanced; }
      set { errorDataEnhanced = value; }
    }

    public AssertCmd(IToken tok, Expr expr, ProofObligationDescription description, QKeyValue kv = null)
      : base(tok, expr, kv)
    {
      errorDataEnhanced = GenerateBoundVarMiningStrategy(expr);
      Description = description;
    }

    public AssertCmd(IToken tok, Expr expr, QKeyValue kv = null)
      : this(tok, expr, new AssertionDescription(), kv) { }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "assert ");
      EmitAttributes(stream, Attributes);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);
      tc.ExpectedLayerRange = Layers?.Count > 0 ? new LayerRange(Layers[0], Layers[^1]) : null;
      Expr.Typecheck(tc);
      tc.ExpectedLayerRange = null;
      Contract.Assert(Expr.Type != null); // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool))
      {
        tc.Error(this, "an asserted expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public static MiningStrategy GenerateBoundVarMiningStrategy(Expr expr)
    {
      Contract.Requires(expr != null);
      List<MiningStrategy> l = new List<MiningStrategy>();
      if (expr != null)
      {
        l = GenerateBoundVarListForMining(expr, l);
      }

      return new ListOfMiningStrategies(l);
    }

    public static List<MiningStrategy> GenerateBoundVarListForMining(Expr expr, List<MiningStrategy> l)
    {
      Contract.Requires(l != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<MiningStrategy>>() != null);

      // go through the origExpr and identify all bound variables in the AST.
      if (expr is LiteralExpr || expr is IdentifierExpr)
      {
        //end recursion
      }
      else if (expr is NAryExpr)
      {
        NAryExpr e = (NAryExpr) expr;
        foreach (Expr arg in e.Args)
        {
          Contract.Assert(arg != null);
          l = GenerateBoundVarListForMining(arg, l);
        }
      }
      else if (expr is OldExpr)
      {
        OldExpr e = (OldExpr) expr;
        l = GenerateBoundVarListForMining(e.Expr, l);
      }
      else if (expr is QuantifierExpr)
      {
        QuantifierExpr qe = (QuantifierExpr) expr;
        List<Variable> vs = qe.Dummies;
        foreach (Variable /*!*/ x in vs)
        {
          Contract.Assert(x != null);
          string name = x.Name;
          if (name.StartsWith("^"))
          {
            name = name.Substring(1);
            List<Expr> exprList = new List<Expr>();
            exprList.Add(new IdentifierExpr(Token.NoToken, x.ToString(), x.TypedIdent.Type));
            MiningStrategy eed = new EEDTemplate("The bound variable " + name + " has the value {0}.", exprList);
            l.Add(eed);
          }
        }

        l = GenerateBoundVarListForMining(qe.Body, l);
      }

      return l;
    }


    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitAssertCmd(this);
    }
  }

  // An AssertCmd that is a loop invariant check before the loop iteration starts
  public class LoopInitAssertCmd : AssertCmd
  {
    public readonly AssertCmd originalAssert;

    public LoopInitAssertCmd(IToken /*!*/ tok, Expr /*!*/ expr, AssertCmd original)
      : base(tok, expr, new InvariantEstablishedDescription())
    {
      this.originalAssert = original;
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
  }

  // An AssertCmd that is a loop invariant check to maintain the invariant after iteration
  public class LoopInvMaintainedAssertCmd : AssertCmd
  {
    public readonly AssertCmd originalAssert;

    public LoopInvMaintainedAssertCmd(IToken /*!*/ tok, Expr /*!*/ expr, AssertCmd original)
      : base(tok, expr, new InvariantMaintainedDescription())
    {
      this.originalAssert = original;
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
  }

  /// <summary>
  /// An AssertCmd that is introduced in translation from the requires on a call.
  /// </summary>
  public class AssertRequiresCmd : AssertCmd
  {
    public CallCmd /*!*/
      Call;

    public Requires /*!*/
      Requires;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Call != null);
      Contract.Invariant(Requires != null);
    }


    public AssertRequiresCmd(CallCmd /*!*/ call, Requires /*!*/ requires)
      : base(call.tok, requires.Condition, requires.Description)
    {
      Contract.Requires(call != null);
      Contract.Requires(requires != null);
      this.Call = call;
      this.Requires = requires;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertRequiresCmd(this);
    }
  }

  /// <summary>
  /// An AssertCmd that is introduced in translation from an ensures
  /// declaration.
  /// </summary>
  public class AssertEnsuresCmd : AssertCmd
  {
    public Ensures /*!*/
      Ensures;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Ensures != null);
    }

    public AssertEnsuresCmd(Ensures /*!*/ ens)
      : base(ens.tok, ens.Condition, ens.Description)
    {
      Contract.Requires(ens != null);
      this.Ensures = ens;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertEnsuresCmd(this);
    }
  }

  public class AssumeCmd : PredicateCmd
  {
    public AssumeCmd(IToken /*!*/ tok, Expr /*!*/ expr)
      : base(tok, expr)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }

    public AssumeCmd(IToken /*!*/ tok, Expr /*!*/ expr, QKeyValue kv)
      : base(tok, expr, kv)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "assume ");
      EmitAttributes(stream, Attributes);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      (this as ICarriesAttributes).ResolveAttributes(rc);
      base.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);
      tc.ExpectedLayerRange = tc.Proc is YieldProcedureDecl decl ? new LayerRange(0, decl.Layer) : null;
      tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl;
      Expr.Typecheck(tc);
      tc.ExpectedLayerRange = null;
      tc.GlobalAccessOnlyInOld = false;
      Contract.Assert(Expr.Type != null); // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool))
      {
        tc.Error(this, "an assumed expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitAssumeCmd(this);
    }
  }

  public class ReturnExprCmd : ReturnCmd
  {
    public Expr /*!*/
      Expr;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Expr != null);
    }

    public ReturnExprCmd(IToken /*!*/ tok, Expr /*!*/ expr)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "return ");
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      Expr.Typecheck(tc);
      Contract.Assert(Expr.Type != null); // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool))
      {
        tc.Error(this, "a return expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Expr.Resolve(rc);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitReturnExprCmd(this);
    }
  }

  public class HavocCmd : Cmd
  {
    private List<IdentifierExpr> /*!*/
      _vars;

    public List<IdentifierExpr> /*!*/ Vars
    {
      get
      {
        Contract.Ensures(Contract.Result<List<IdentifierExpr>>() != null);
        return this._vars;
      }
      set
      {
        Contract.Requires(value != null);
        this._vars = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._vars != null);
    }

    public HavocCmd(IToken /*!*/ tok, List<IdentifierExpr> /*!*/ vars)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(vars != null);
      this._vars = vars;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "havoc ");
      Vars.Emit(stream, true);
      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      foreach (IdentifierExpr /*!*/ ide in Vars)
      {
        Contract.Assert(ide != null);
        ide.Resolve(rc);
      }
    }

    public override void AddAssignedVariables(List<Variable> vars)
    {
      //Contract.Requires(vars != null);
      foreach (IdentifierExpr /*!*/ e in this.Vars)
      {
        Contract.Assert(e != null);
        vars.Add(e.Decl);
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (IdentifierExpr ie in Vars)
      {
        ie.Typecheck(tc);
      }

      this.CheckAssignments(tc);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitHavocCmd(this);
    }
  }

  //---------------------------------------------------------------------
  // Transfer commands
  [ContractClass(typeof(TransferCmdContracts))]
  public abstract class TransferCmd : Absy
  {
    public ProofObligationDescription Description { get; set; } = new PostconditionDescription();

    internal TransferCmd(IToken /*!*/ tok)
      : base(tok)
    {
      Contract.Requires(tok != null);
    }

    public abstract void Emit(TokenTextWriter /*!*/ stream, int level);

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      // nothing to typecheck
    }

    public override string ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      System.IO.StringWriter buffer = new System.IO.StringWriter();
      using TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false, false, PrintOptions.Default);
      this.Emit(stream, 0);

      return buffer.ToString();
    }
  }

  [ContractClassFor(typeof(TransferCmd))]
  public abstract class TransferCmdContracts : TransferCmd
  {
    public TransferCmdContracts() : base(null)
    {
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }
  }

  public class ReturnCmd : TransferCmd
  {
    public ReturnCmd(IToken /*!*/ tok)
      : base(tok)
    {
      Contract.Requires(tok != null);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.WriteLine(this, level, "return;");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      // nothing to resolve
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitReturnCmd(this);
    }
  }

  public class GotoCmd : TransferCmd
  {
    [Rep] public List<String> labelNames;
    [Rep] public List<Block> labelTargets;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(labelNames == null || labelTargets == null || labelNames.Count == labelTargets.Count);
    }

    [NotDelayed]
    public GotoCmd(IToken /*!*/ tok, List<String> /*!*/ labelSeq)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(labelSeq != null);
      this.labelNames = labelSeq;
    }

    public GotoCmd(IToken /*!*/ tok, List<String> /*!*/ labelSeq, List<Block> /*!*/ blockSeq)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(labelSeq != null);
      Contract.Requires(blockSeq != null);
      Debug.Assert(labelSeq.Count == blockSeq.Count);
      for (int i = 0; i < labelSeq.Count; i++)
      {
        Debug.Assert(Equals(labelSeq[i], cce.NonNull(blockSeq[i]).Label));
      }

      this.labelNames = labelSeq;
      this.labelTargets = blockSeq;
    }

    public GotoCmd(IToken /*!*/ tok, List<Block> /*!*/ blockSeq)
      : base(tok)
    {
      //requires (blockSeq[i] != null ==> blockSeq[i].Label != null);
      Contract.Requires(tok != null);
      Contract.Requires(blockSeq != null);
      List<String> labelSeq = new List<String>();
      for (int i = 0; i < blockSeq.Count; i++)
      {
        labelSeq.Add(cce.NonNull(blockSeq[i]).Label);
      }

      this.labelNames = labelSeq;
      this.labelTargets = blockSeq;
    }

    public void AddTarget(Block b)
    {
      Contract.Requires(b != null);
      Contract.Requires(b.Label != null);
      Contract.Requires(this.labelTargets != null);
      Contract.Requires(this.labelNames != null);
      this.labelTargets.Add(b);
      this.labelNames.Add(b.Label);
    }

    public void AddTargets(IEnumerable<Block> blocks)
    {
      Contract.Requires(blocks != null);
      Contract.Requires(cce.NonNullElements(blocks));
      Contract.Requires(this.labelTargets != null);
      Contract.Requires(this.labelNames != null);
      foreach (var block in blocks)
      {
        AddTarget(block);
      }
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      Contract.Assume(this.labelNames != null);
      stream.Write(this, level, "goto ");
      if (stream.Options.PrintWithUniqueASTIds)
      {
        if (labelTargets == null)
        {
          string sep = "";
          foreach (string name in labelNames)
          {
            stream.Write("{0}{1}^^{2}", sep, "NoDecl", name);
            sep = ", ";
          }
        }
        else
        {
          string sep = "";
          foreach (Block /*!*/ b in labelTargets)
          {
            Contract.Assert(b != null);
            stream.Write("{0}h{1}^^{2}", sep, b.GetHashCode(), b.Label);
            sep = ", ";
          }
        }
      }
      else
      {
        labelNames.Emit(stream);
      }

      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Contract.Ensures(labelTargets != null);
      if (labelTargets != null)
      {
        // already resolved
        return;
      }

      Contract.Assume(this.labelNames != null);
      labelTargets = new List<Block>();
      foreach (string /*!*/ lbl in labelNames)
      {
        Contract.Assert(lbl != null);
        Block b = rc.LookUpBlock(lbl);
        if (b == null)
        {
          rc.Error(this, "goto to unknown block: {0}", lbl);
        }
        else
        {
          labelTargets.Add(b);
        }
      }

      Debug.Assert(rc.ErrorCount > 0 || labelTargets.Count == labelNames.Count);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitGotoCmd(this);
    }
  }
}
