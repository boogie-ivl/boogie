using System;
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using System.IO;
using System.Threading.Tasks;
using Set = Microsoft.Boogie.GSet<object>;

namespace VC
{
  public class VCGenException : Exception
  {
    public VCGenException(string s)
      : base(s)
    {
    }
  }

  [ContractClassFor(typeof(ConditionGeneration))]
  public abstract class ConditionGenerationContracts : ConditionGeneration
  {
    public override Task<VcOutcome> VerifyImplementation(ImplementationRun run, VerifierCallback callback,
      CancellationToken cancellationToken)
    {
      Contract.Requires(run != null);
      Contract.Requires(callback != null);
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      throw new NotImplementedException();
    }

    public ConditionGenerationContracts(Program program, CheckerPool checkerPool)
      : base(program, checkerPool)
    {
    }
  }

  [ContractClass(typeof(ConditionGenerationContracts))]
  public abstract class ConditionGeneration : IDisposable
  {
    public static VcOutcome ProverInterfaceOutcomeToConditionGenerationOutcome(SolverOutcome outcome)
    {
      switch (outcome)
      {
        case SolverOutcome.Invalid:
          return VcOutcome.Errors;
        case SolverOutcome.OutOfMemory:
          return VcOutcome.OutOfMemory;
        case SolverOutcome.TimeOut:
          return VcOutcome.TimedOut;
        case SolverOutcome.OutOfResource:
          return VcOutcome.OutOfResource;
        case SolverOutcome.Undetermined:
          return VcOutcome.Inconclusive;
        case SolverOutcome.Valid:
          return VcOutcome.Correct;
      }

      return VcOutcome.Inconclusive; // unreachable but the stupid compiler does not understand
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullDictionaryAndValues(incarnationOriginMap));
      Contract.Invariant(program != null);
    }

    public TimeSpan TotalProverElapsedTime { get; set; }
    public int CumulativeAssertionCount; // for statistics
    public int ResourceCount;
    
    private bool _disposed;

    protected Implementation currentImplementation;

    public List<Variable> CurrentLocalVariables { get; set; } = null;

    // shared across each implementation; created anew for each implementation
    protected Dictionary<Variable, int> variable2SequenceNumber;

    public Dictionary<Incarnation, Absy> incarnationOriginMap = new Dictionary<Incarnation, Absy>();

    public Program program;
    public CheckerPool CheckerPool { get; }

    public ConditionGeneration(Program program, CheckerPool checkerPool)
    {
      Contract.Requires(program != null && checkerPool != null);
      this.program = program;
      CheckerPool = checkerPool;
    }

    /// <summary>
    /// Takes an implementation and constructs a verification condition and sends
    /// it to the theorem prover.
    /// Returns null if "impl" is correct.  Otherwise, returns a list of counterexamples,
    /// each counterexample consisting of an array of labels.
    /// </summary>
    /// <param name="run"></param>
    /// <param name="batchCompletedObserver"></param>
    /// <param name="cancellationToken"></param>
    /// <param name="impl"></param>
    public async Task<(VcOutcome, List<Counterexample> errors, List<VerificationRunResult> vcResults)> VerifyImplementation2(
      ImplementationRun run, CancellationToken cancellationToken)
    {
      Contract.Requires(run != null);

      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
      Helpers.ExtraTraceInformation(Options, "Starting implementation verification");

      var collector = new VerificationResultCollector(Options);
      VcOutcome vcOutcome = await VerifyImplementation(run, collector, cancellationToken);
      var /*?*/ errors = new List<Counterexample>();
      if (vcOutcome is VcOutcome.Errors or VcOutcome.TimedOut or VcOutcome.OutOfMemory or VcOutcome.OutOfResource) {
        errors = collector.examples.ToList();
      }

      Helpers.ExtraTraceInformation(Options, "Finished implementation verification");
      return (vcOutcome, errors, collector.vcResults.ToList());
    }

    private VCGenOptions Options => CheckerPool.Options;

    public abstract Task<VcOutcome> VerifyImplementation(ImplementationRun run, VerifierCallback callback,
      CancellationToken cancellationToken);

    /////////////////////////////////// Common Methods and Classes //////////////////////////////////////////

    #region Methods for injecting pre- and postconditions

    private static void
      ThreadInCodeExpr(Implementation impl,
        Block targetBlock,
        CodeExpr codeExpr,
        bool replaceWithAssert,
        TokenTextWriter debugWriter)
    {
      Contract.Requires(impl != null);
      Contract.Requires(codeExpr != null);
      Contract.Requires(targetBlock != null);
      // Go through codeExpr and for all blocks that have a "return e"
      // as their transfer command:
      //   Replace all "return e" with "assert/assume e"
      //   Change the transfer command to "goto targetBlock"
      // Then add all of the blocks in codeExpr to the implementation (at the end)
      foreach (Block b in codeExpr.Blocks)
      {
        Contract.Assert(b != null);
        ReturnExprCmd rec = b.TransferCmd as ReturnExprCmd;
        if (rec != null)
        {
          // otherwise it is a goto command
          if (replaceWithAssert)
          {
            Ensures ens = new Ensures(rec.tok, false, rec.Expr, null);
            Contract.Assert(ens != null);
            Cmd c = new AssertEnsuresCmd(ens);
            Contract.Assert(c != null);
            b.Cmds.Add(c);
          }
          else
          {
            b.Cmds.Add(new AssumeCmd(rec.tok, rec.Expr));
          }

          b.TransferCmd = new GotoCmd(Token.NoToken,
            new List<String> {targetBlock.Label},
            new List<Block> {targetBlock});
          targetBlock.Predecessors.Add(b);
        }

        impl.Blocks.Add(b);
      }

      if (debugWriter != null)
      {
        codeExpr.Emit(debugWriter, 1, false);
      }

      return;
    }

    private static void AddAsPrefix(Block b, List<Cmd> cs)
    {
      Contract.Requires(b != null);
      Contract.Requires(cs != null);
      List<Cmd> newCommands = new List<Cmd>();
      newCommands.AddRange(cs);
      newCommands.AddRange(b.Cmds);
      b.Cmds = newCommands;
    }


    /// <summary>
    /// Modifies an implementation by prepending it with startCmds and then, as assume
    /// statements, all preconditions.  Insert new blocks as needed, and adjust impl.Blocks[0]
    /// accordingly to make it the new implementation entry block.
    /// </summary>
    /// <param name="impl"></param>
    /// <param name="startCmds"></param>
    protected static void InjectPreconditions(VCGenOptions options, ImplementationRun run, [Captured] List<Cmd> startCmds)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(startCmds != null);
      Contract.Requires(impl.Proc != null);

      TokenTextWriter debugWriter = null;
      if (options.PrintWithUniqueASTIds)
      {
        debugWriter = new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options);
        debugWriter.WriteLine("Effective precondition:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap(options));
      string blockLabel = "PreconditionGeneratedEntry";

      Block origStartBlock = impl.Blocks[0];
      Block insertionPoint = new Block(
        new Token(-17, -4), blockLabel, startCmds,
        new GotoCmd(impl.tok, new List<String> {origStartBlock.Label}, new List<Block> {origStartBlock}));

      impl.Blocks.Insert(0, insertionPoint); // make insertionPoint the start block

      // (free and checked) requires clauses
      foreach (Requires req in impl.Proc.Requires)
        // invariant:  insertionPoint.TransferCmd is "goto origStartBlock;", but origStartBlock.Predecessors has not yet been updated
      {
        Contract.Assert(req != null);
        Expr e = Substituter.Apply(formalProcImplSubst, req.Condition);
        AssumeCmd c = new AssumeCmd(req.tok, e, CivlAttributes.ApplySubstitutionToPoolHints(formalProcImplSubst, req.Attributes));
        // Copy any {:id ...} from the precondition to the assumption, so
        // we can track it while analyzing verification coverage.
        (c as ICarriesAttributes).CopyIdFrom(req.tok, req);
        c.IrrelevantForChecksumComputation = true;
        insertionPoint.Cmds.Add(c);
        if (debugWriter != null)
        {
          c.Emit(debugWriter, 1);
        }
      }

      origStartBlock.Predecessors.Add(insertionPoint);

      if (impl.ExplicitAssumptionAboutCachedPrecondition != null)
      {
        insertionPoint.Cmds.Add(impl.ExplicitAssumptionAboutCachedPrecondition);
      }

      if (debugWriter != null)
      {
        debugWriter.WriteLine();
      }
    }

    /// <summary>
    /// Modifies an implementation by inserting all postconditions
    /// as assert statements at the end of the implementation
    /// Returns the possibly-new unified exit block of the implementation
    /// </summary>
    /// <param name="impl"></param>
    /// <param name="unifiedExitblock">The unified exit block that has
    /// already been constructed for the implementation (and so
    /// is already an element of impl.Blocks)
    /// </param>
    protected static void InjectPostConditions(VCGenOptions options, ImplementationRun run, Block unifiedExitBlock,
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(unifiedExitBlock != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Requires(impl.Proc != null);
      Contract.Requires(unifiedExitBlock.TransferCmd is ReturnCmd);

      TokenTextWriter debugWriter = null;
      if (options.PrintWithUniqueASTIds)
      {
        debugWriter = new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options);
        debugWriter.WriteLine("Effective postcondition:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap(options));

      // (free and checked) ensures clauses
      foreach (Ensures ens in impl.Proc.Ensures)
      {
        Contract.Assert(ens != null);

        if (!ens.Free)
        {
          Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
          Ensures ensCopy = (Ensures) cce.NonNull(ens.Clone());
          ensCopy.Condition = e;
          AssertEnsuresCmd c = new AssertEnsuresCmd(ensCopy);
          c.ErrorDataEnhanced = ensCopy.ErrorDataEnhanced;
          // Copy any {:id ...} from the postcondition to the assumption, so
          // we can track it while analyzing verification coverage.
          (c as ICarriesAttributes).CopyIdFrom(ens.tok, ens);
          unifiedExitBlock.Cmds.Add(c);
          if (debugWriter != null)
          {
            c.Emit(debugWriter, 1);
          }
        }
        else if (ens.CanAlwaysAssume())
        {
          Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
          unifiedExitBlock.Cmds.Add(new AssumeCmd(ens.tok, e));
        }
        else
        {
          // skip free ensures if it doesn't have the :always_assume attr
        }
      }

      if (debugWriter != null)
      {
        debugWriter.WriteLine();
      }
    }


    /// <summary>
    /// Get the pre-condition of an implementation, including the where clauses from the in-parameters.
    /// </summary>
    /// <param name="impl"></param>
    protected static List<Cmd> GetPre(VCGenOptions options, ImplementationRun run)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);


      TokenTextWriter debugWriter = null;
      if (options.PrintWithUniqueASTIds)
      {
        debugWriter = new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options);
        debugWriter.WriteLine("Effective precondition:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap(options));
      List<Cmd> pre = new List<Cmd>();

      // (free and checked) requires clauses
      foreach (Requires req in impl.Proc.Requires)
      {
        Contract.Assert(req != null);
        Expr e = Substituter.Apply(formalProcImplSubst, req.Condition);
        Contract.Assert(e != null);
        Cmd c = new AssumeCmd(req.tok, e);
        Contract.Assert(c != null);
        pre.Add(c);

        if (debugWriter != null)
        {
          c.Emit(debugWriter, 1);
        }
      }

      if (debugWriter != null)
      {
        debugWriter.WriteLine();
      }

      return pre;
    }

    /// <summary>
    /// Get the post-condition of an implementation.
    /// </summary>
    /// <param name="impl"></param>
    protected static List<Cmd> GetPost(VCGenOptions options, ImplementationRun run)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      if (options.PrintWithUniqueASTIds)
      {
        options.OutputWriter.WriteLine("Effective postcondition:");
      }

      // Construct an Expr for the post-condition
      Substitution formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap(options));
      List<Cmd> post = new List<Cmd>();
      foreach (Ensures ens in impl.Proc.Ensures)
      {
        Contract.Assert(ens != null);
        if (!ens.Free)
        {
          Expr e = Substituter.Apply(formalProcImplSubst, ens.Condition);
          Contract.Assert(e != null);
          Ensures ensCopy = cce.NonNull((Ensures) ens.Clone());
          ensCopy.Condition = e;
          Cmd c = new AssertEnsuresCmd(ensCopy);
          ((AssertEnsuresCmd) c).ErrorDataEnhanced = ensCopy.ErrorDataEnhanced;
          post.Add(c);

          if (options.PrintWithUniqueASTIds)
          {
            c.Emit(new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options), 1);
          }
        }
      }

      if (options.PrintWithUniqueASTIds)
      {
        options.OutputWriter.WriteLine();
      }

      return post;
    }

    /// <summary>
    /// Get the where clauses from the in- and out-parameters as
    /// a sequence of assume commands.
    /// As a side effect, this method adds these where clauses to the out parameters.
    /// </summary>
    /// <param name="impl"></param>
    protected static List<Cmd> GetParamWhereClauses(VCGenOptions options, ImplementationRun run)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(impl.Proc != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      TokenTextWriter debugWriter = null;
      if (options.PrintWithUniqueASTIds)
      {
        debugWriter = new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options);
        debugWriter.WriteLine("Effective precondition from where-clauses:");
      }

      Substitution formalProcImplSubst = Substituter.SubstitutionFromDictionary(impl.GetImplFormalMap(options));
      List<Cmd> whereClauses = new List<Cmd>();

      // where clauses of in-parameters
      foreach (Formal f in impl.Proc.InParams)
      {
        Contract.Assert(f != null);
        if (f.TypedIdent.WhereExpr != null)
        {
          Expr e = Substituter.Apply(formalProcImplSubst, f.TypedIdent.WhereExpr);
          Cmd c = new AssumeCmd(f.tok, e);
          whereClauses.Add(c);

          if (debugWriter != null)
          {
            c.Emit(debugWriter, 1);
          }
        }
      }

      // where clauses of out-parameters
      Contract.Assert(impl.OutParams.Count == impl.Proc.OutParams.Count);
      for (int i = 0; i < impl.OutParams.Count; i++)
      {
        Variable f = cce.NonNull(impl.Proc.OutParams[i]);
        if (f.TypedIdent.WhereExpr != null)
        {
          Expr e = Substituter.Apply(formalProcImplSubst, f.TypedIdent.WhereExpr);
          Cmd c = new AssumeCmd(f.tok, e);
          whereClauses.Add(c);

          Variable fi = cce.NonNull(impl.OutParams[i]);
          Contract.Assume(fi.TypedIdent.WhereExpr == null);
          fi.TypedIdent.WhereExpr = e;

          if (debugWriter != null)
          {
            c.Emit(debugWriter, 1);
          }
        }
      }

      if (debugWriter != null)
      {
        debugWriter.WriteLine();
      }

      return whereClauses;
    }

    protected static void RestoreParamWhereClauses(Implementation impl)
    {
      Contract.Requires(impl != null);
      // We no longer need the where clauses on the out parameters, so we remove them to restore the situation from before VC generation
      foreach (Formal f in impl.OutParams)
      {
        Contract.Assert(f != null);
        f.TypedIdent.WhereExpr = null;
      }
    }

    #endregion
    
    public virtual void Close()
    {
    }


    public static void EmitImpl(VCGenOptions options, ImplementationRun run, bool printDesugarings, IEnumerable<Block> overrideBlocks = null)
    {
      var impl = run.Implementation;
      overrideBlocks ??= impl.Blocks;
      
      Contract.Requires(impl != null);
      bool oldPrintDesugaringSetting = options.PrintDesugarings;
      options.PrintDesugarings = printDesugarings;
      var writer = new TokenTextWriter("<console>", run.OutputWriter, /*setTokens=*/ false, /*pretty=*/ false, options);
      impl.EmitImplementation(writer, 0, overrideBlocks, true);
      options.PrintDesugarings = oldPrintDesugaringSetting;
    }


    protected Block GenerateUnifiedExit(Implementation impl, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins)
    {
      Contract.Requires(impl != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Ensures(Contract.Result<Block>() != null);

      Contract.Ensures(Contract.Result<Block>().TransferCmd is ReturnCmd);
      Block /*?*/
        exitBlock = null;

      #region Create a unified exit block, if there's more than one

      {
        int returnBlocks = 0;
        foreach (Block b in impl.Blocks)
        {
          if (b.TransferCmd is ReturnCmd)
          {
            exitBlock = b;
            returnBlocks++;
          }
        }

        if (returnBlocks > 1)
        {
          string unifiedExitLabel = "GeneratedUnifiedExit";
          var unifiedExit = new Block(new Token(-17, -4), unifiedExitLabel, new List<Cmd>(),
            new ReturnCmd(impl.StructuredStmts != null ? impl.StructuredStmts.EndCurly : Token.NoToken));
          Contract.Assert(unifiedExit != null);
          foreach (Block b in impl.Blocks)
          {
            if (b.TransferCmd is ReturnCmd returnCmd)
            {
              List<String> labels = new List<String>();
              labels.Add(unifiedExitLabel);
              List<Block> bs = new List<Block>();
              bs.Add(unifiedExit);
              GotoCmd go = new GotoCmd(returnCmd.tok, labels, bs);
              gotoCmdOrigins[go] = returnCmd;
              b.TransferCmd = go;
              unifiedExit.Predecessors.Add(b);
            }
          }

          exitBlock = unifiedExit;
          impl.Blocks.Add(unifiedExit);
        }

        Contract.Assert(exitBlock != null);
      }
      return exitBlock;

      #endregion
    }

    public static void ResetPredecessors(List<Block> blocks)
    {
      Contract.Requires(blocks != null);
      foreach (Block b in blocks)
      {
        Contract.Assert(b != null);
        b.Predecessors = new List<Block>();
      }

      foreach (Block b in blocks)
      {
        Contract.Assert(b != null);
        foreach (Block ch in b.Exits())
        {
          Contract.Assert(ch != null);
          ch.Predecessors.Add(b);
        }
      }
    }

    protected Variable CreateIncarnation(Variable x, Absy a)
    {
      Contract.Requires(this.variable2SequenceNumber != null);
      Contract.Requires(this.CurrentLocalVariables != null);
      Contract.Requires(a is Block || a is AssignCmd || a is HavocCmd);

      Contract.Requires(x != null);
      Contract.Ensures(Contract.Result<Variable>() != null);

      int currentIncarnationNumber =
        variable2SequenceNumber.ContainsKey(x)
          ? variable2SequenceNumber[x]
          : -1;
      Variable v = new Incarnation(x, currentIncarnationNumber + 1);
      variable2SequenceNumber[x] = currentIncarnationNumber + 1;
      CurrentLocalVariables.Add(v);
      incarnationOriginMap.Add((Incarnation) v, a);
      return v;
    }

    /// <summary>
    /// Compute the incarnation map at the beginning of block "b" from the incarnation blocks of the
    /// predecessors of "b".
    ///
    /// The predecessor map b.map for block "b" is defined as follows:
    ///   b.map.Domain == Union{Block p in b.predecessors; p.map.Domain}
    ///   Forall{Variable v in b.map.Domain;
    ///              b.map[v] == (v in Intersection{Block p in b.predecessors; p.map}.Domain
    ///                           ?  b.predecessors[0].map[v]
    ///                           :  new Variable())}
    /// Every variable that b.map maps to a fresh variable requires a fixup in all predecessor blocks.
    /// </summary>
    /// <param name="b"></param>
    /// <param name="block2Incarnation">Gives incarnation maps for b's predecessors.</param>
    /// <returns></returns>
    protected Dictionary<Variable, Expr> ComputeIncarnationMap(Block b,
      Dictionary<Block, Dictionary<Variable, Expr>> block2Incarnation)
    {
      Contract.Requires(b != null);
      Contract.Requires(block2Incarnation != null);
      Contract.Ensures(Contract.Result<Dictionary<Variable, Expr>>() != null);

      if (b.Predecessors.Count == 0)
      {
        return new Dictionary<Variable, Expr>();
      }

      Dictionary<Variable, Expr> incarnationMap = null;
      Set /*Variable*/
        fixUps = new Set /*Variable*/();
      foreach (Block pred in b.Predecessors)
      {
        Contract.Assert(pred != null);
        Contract.Assert(block2Incarnation
          .ContainsKey(pred)); // otherwise, Passive Transformation found a block whose predecessors have not been processed yet
        Dictionary<Variable, Expr> predMap = (Dictionary<Variable, Expr>) block2Incarnation[pred];
        Contract.Assert(predMap != null);
        if (incarnationMap == null)
        {
          incarnationMap = new Dictionary<Variable, Expr>(predMap);
          continue;
        }

        ArrayList /*Variable*/
          conflicts = new ArrayList /*Variable*/();
        foreach (Variable v in incarnationMap.Keys)
        {
          Contract.Assert(v != null);
          if (!predMap.ContainsKey(v))
          {
            // conflict!!
            conflicts.Add(v);
            fixUps.Add(v);
          }
        }

        // Now that we're done with enumeration, we'll do all the removes
        foreach (Variable v in conflicts)
        {
          Contract.Assert(v != null);
          incarnationMap.Remove(v);
        }

        foreach (Variable v in predMap.Keys)
        {
          Contract.Assert(v != null);
          if (!incarnationMap.ContainsKey(v))
          {
            // v was not in the domain of the predecessors seen so far, so it needs to be fixed up
            fixUps.Add(v);
          }
          else
          {
            // v in incarnationMap ==> all pred blocks (up to now) all agree on its incarnation
            if (predMap[v] != incarnationMap[v])
            {
              // conflict!!
              incarnationMap.Remove(v);
              fixUps.Add(v);
            }
          }
        }
      }

      #region Second, for all variables in the fixups list, introduce a new incarnation and push it back into the preds.

      foreach (Variable v in fixUps)
      {
        Contract.Assert(v != null);
        if (!b.IsLive(v))
        {
          continue;
        }

        Variable v_prime = CreateIncarnation(v, b);
        IdentifierExpr ie = new IdentifierExpr(v_prime.tok, v_prime);
        Contract.Assert(incarnationMap != null);
        incarnationMap[v] = ie;
        foreach (Block pred in b.Predecessors)
        {
          Contract.Assert(pred != null);

          #region Create an assume command equating v_prime with its last incarnation in pred

          #region Create an identifier expression for the last incarnation in pred

          Dictionary<Variable, Expr> predMap = (Dictionary<Variable, Expr>) cce.NonNull(block2Incarnation[pred]);

          Expr pred_incarnation_exp;
          Expr o = predMap.ContainsKey(v) ? predMap[v] : null;
          if (o == null)
          {
            Variable predIncarnation = v;
            IdentifierExpr ie2 = new IdentifierExpr(predIncarnation.tok, predIncarnation);
            pred_incarnation_exp = ie2;
          }
          else
          {
            pred_incarnation_exp = o;
          }

          #endregion

          #region Create an identifier expression for the new incarnation

          IdentifierExpr v_prime_exp = new IdentifierExpr(v_prime.tok, v_prime);

          #endregion

          #region Create the assume command itself

          AssumeCmd ac = new AssumeCmd(v.tok,
            TypedExprEq(v_prime_exp, pred_incarnation_exp, v_prime.Name.Contains("a##cached##")));
          pred.Cmds.Add(ac);

          #endregion

          #endregion
        }
      }

      #endregion

      Contract.Assert(incarnationMap != null);
      return incarnationMap;
    }

    Dictionary<Variable, Expr>
      preHavocIncarnationMap =
        null; // null = the previous command was not an HashCmd. Otherwise, a *copy* of the map before the havoc statement

    protected void TurnIntoPassiveBlock(TextWriter traceWriter, Block b, Dictionary<Variable, Expr> incarnationMap, ModelViewInfo mvInfo,
      Substitution oldFrameSubst, MutableVariableCollector variableCollector, Dictionary<Cmd, List<object>> debugInfos, byte[] currentChecksum = null)
    {
      Contract.Requires(b != null);
      Contract.Requires(incarnationMap != null);
      Contract.Requires(mvInfo != null);
      Contract.Requires(oldFrameSubst != null);

      #region Walk forward over the commands in this block and convert them to passive commands

      List<Cmd> passiveCmds = new List<Cmd>();
      foreach (Cmd c in b.Cmds)
      {
        Contract.Assert(
          c != null); // walk forward over the commands because the map gets modified in a forward direction
        ChecksumHelper.ComputeChecksums(Options, c, currentImplementation, variableCollector.UsedVariables, currentChecksum);
        variableCollector.Visit(c);
        currentChecksum = c.Checksum;
        TurnIntoPassiveCmd(traceWriter, c, b, incarnationMap, oldFrameSubst, passiveCmds, mvInfo, debugInfos);
      }

      b.Checksum = currentChecksum;
      b.Cmds = passiveCmds;

      if (b.TransferCmd is ReturnExprCmd)
      {
        ReturnExprCmd rec = (ReturnExprCmd) b.TransferCmd.Clone();
        Substitution incarnationSubst = Substituter.SubstitutionFromDictionary(incarnationMap);
        rec.Expr = Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, rec.Expr);
        b.TransferCmd = rec;
      }

      #endregion
    }

    protected Dictionary<Variable, Expr> Convert2PassiveCmd(ImplementationRun run, ModelViewInfo mvInfo)
    {
      Contract.Requires(run != null);
      Contract.Requires(mvInfo != null);

      var implementation = run.Implementation;
      currentImplementation = run.Implementation;

      var start = DateTime.UtcNow;

      Dictionary<Variable, Expr> r = ConvertBlocks2PassiveCmd(run.OutputWriter, implementation.Blocks, implementation.Proc.Modifies, mvInfo, implementation.debugInfos);

      var end = DateTime.UtcNow;

      if (Options.TraceCachingForDebugging)
      {
        run.OutputWriter.WriteLine("Turned implementation into passive commands within {0:F0} ms.\n",
          end.Subtract(start).TotalMilliseconds);

        var tokTxtWr = new TokenTextWriter("<console>", run.OutputWriter, false, false, Options);
        var pd = Options.PrintDesugarings;
        var pu = Options.PrintUnstructured;
        Options.PrintDesugarings = true;
        Options.PrintUnstructured = 1;
        implementation.Emit(tokTxtWr, 0);
        Options.PrintDesugarings = pd;
        Options.PrintUnstructured = pu;
      }

      currentImplementation = null;

      RestoreParamWhereClauses(implementation);

      #region Debug Tracing

      if (Options.TraceVerify)
      {
        Options.OutputWriter.WriteLine("after conversion to passive commands");
        EmitImpl(Options, run, true);
      }

      #endregion

      return r;
    }

    protected Dictionary<Variable, Expr> ConvertBlocks2PassiveCmd(TextWriter traceWriter, List<Block> blocks, List<IdentifierExpr> modifies,
      ModelViewInfo mvInfo, Dictionary<Cmd, List<object>> debugInfos)
    {
      Contract.Requires(blocks != null);
      Contract.Requires(modifies != null);
      Contract.Requires(mvInfo != null);

      #region Convert to Passive Commands

      #region Topological sort -- need to process in a linearization of the partial order

      Graph<Block> dag = Program.GraphFromBlocks(blocks);
      IEnumerable sortedNodes;
      if (Options.ModifyTopologicalSorting)
      {
        sortedNodes = dag.TopologicalSort(true);
      }
      else
      {
        sortedNodes = dag.TopologicalSort();
      }

      Contract.Assert(sortedNodes != null);

      #endregion

      Substitution oldFrameSubst = ComputeOldExpressionSubstitution(modifies);

      // Now we can process the nodes in an order so that we're guaranteed to have
      // processed all of a node's predecessors before we process the node.
      Dictionary<Block, Dictionary<Variable, Expr>> block2Incarnation =
        new Dictionary<Block, Dictionary<Variable, Expr>>();
      Block exitBlock = null;
      Dictionary<Variable, Expr> exitIncarnationMap = null;
      var variableCollectors = new Dictionary<Block, MutableVariableCollector>();
      foreach (Block b in sortedNodes)
      {
        Contract.Assert(b != null);
        Contract.Assert(!block2Incarnation.ContainsKey(b));
        Dictionary<Variable, Expr> incarnationMap = ComputeIncarnationMap(b, block2Incarnation);

        // b.liveVarsBefore has served its purpose in the just-finished call to ComputeIncarnationMap; null it out.
        b.liveVarsBefore = null;

        // Decrement the succCount field in each predecessor. Once the field reaches zero in any block,
        // all its successors have been passified.  Consequently, its entry in block2Incarnation can be removed.
        byte[] currentChecksum = null;
        var mvc = new MutableVariableCollector();
        variableCollectors[b] = mvc;
        foreach (Block p in b.Predecessors)
        {
          p.succCount--;
          if (p.Checksum != null)
          {
            // Compute the checksum based on the checksums of the predecessor. The order should not matter.
            currentChecksum = ChecksumHelper.CombineChecksums(p.Checksum, currentChecksum, true);
          }

          mvc.AddUsedVariables(variableCollectors[p].UsedVariables);
          if (p.succCount == 0)
          {
            block2Incarnation.Remove(p);
          }
        }

        #region Each block's map needs to be available to successor blocks

        GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
        if (gotoCmd == null)
        {
          b.succCount = 0;
        }
        else
        {
          // incarnationMap needs to be added only if there is some successor of b
          b.succCount = gotoCmd.labelNames.Count;
          block2Incarnation.Add(b, incarnationMap);
        }

        #endregion Each block's map needs to be available to successor blocks

        TurnIntoPassiveBlock(traceWriter, b, incarnationMap, mvInfo, oldFrameSubst, mvc, debugInfos, currentChecksum);
        exitBlock = b;
        exitIncarnationMap = incarnationMap;
      }

      variableCollectors.Clear();

      // Verify that exitBlock is indeed the unique exit block
      Contract.Assert(exitBlock != null);
      Contract.Assert(exitBlock.TransferCmd is ReturnCmd);

      #endregion Convert to Passive Commands

      return exitIncarnationMap;
    }

    /// <summary>
    /// Compute the substitution for old expressions.
    /// </summary>
    protected static Substitution ComputeOldExpressionSubstitution(List<IdentifierExpr> modifies)
    {
      Dictionary<Variable, Expr> oldFrameMap = new Dictionary<Variable, Expr>();
      foreach (IdentifierExpr ie in modifies)
      {
        Contract.Assert(ie != null);
        if (!oldFrameMap.ContainsKey(cce.NonNull(ie.Decl)))
        {
          oldFrameMap.Add(ie.Decl, ie);
        }
      }

      return Substituter.SubstitutionFromDictionary(oldFrameMap);
    }

    public enum CachingAction : byte
    {
      DoNothingToAssert,
      MarkAsPartiallyVerified,
      MarkAsFullyVerified,
      RecycleError,
      AssumeNegationOfAssumptionVariable,
      DropAssume
    }

    public long[] CachingActionCounts;

    void TraceCachingAction(TextWriter traceWriter, Cmd cmd, CachingAction action)
    {
      if (Options.TraceCachingForTesting) {
        var tokTxtWr = new TokenTextWriter("<console>", traceWriter, false, false, Options);
        var loc = cmd.tok != null && cmd.tok != Token.NoToken
          ? string.Format("{0}({1},{2})", cmd.tok.filename, cmd.tok.line, cmd.tok.col)
          : "<unknown location>";
        traceWriter.Write("Processing command (at {0}) ", loc);
        cmd.Emit(tokTxtWr, 0);
        traceWriter.WriteLine("  >>> {0}", action);
      }

      if (Options.TraceCachingForBenchmarking && CachingActionCounts != null)
      {
        Interlocked.Increment(ref CachingActionCounts[(int) action]);
      }
    }

    private void AddDebugInfo(Cmd c, Dictionary<Variable, Expr> incarnationMap, List<Cmd> passiveCmds, Dictionary<Cmd, List<object>> debugInfos)
    {
      if (c is ICarriesAttributes cmd)
      {
        var debugExprs = new List<object>();
        QKeyValue current = cmd.Attributes;
        while (current != null)
        {
          if (current.Key == "print")
          {
            foreach (var param in current.Params)
            {
              if (param is IdentifierExpr identifierExpr)
              {
                if (incarnationMap.ContainsKey(identifierExpr.Decl))
                {
                  debugExprs.Add(incarnationMap[identifierExpr.Decl]);
                }
                else
                {
                  debugExprs.Add(identifierExpr);
                }
              }
              else
              {
                debugExprs.Add(param);
              }
            }
            debugExprs.Add("\n");
          }
          current = current.Next;
        }
        if (debugExprs.Count == 0)
        {
          return;
        }
        var debugCmd = new AssumeCmd(Token.NoToken, Expr.True);
        passiveCmds.Add(debugCmd);
        debugInfos.Add(debugCmd, debugExprs);
      }
    }

    /// <summary>
    /// Turn a command into a passive command, and it remembers the previous step, to see if it is a havoc or not.
    /// In that case, it remembers the incarnation map BEFORE the havoc.
    /// Meanwhile, record any information needed to later reconstruct a model view.
    /// </summary>
    protected void TurnIntoPassiveCmd(TextWriter traceWriter, Cmd c, Block enclosingBlock, Dictionary<Variable, Expr> incarnationMap, Substitution oldFrameSubst,
      List<Cmd> passiveCmds, ModelViewInfo mvInfo, Dictionary<Cmd, List<object>> debugInfos)
    {
      Contract.Requires(c != null);
      Contract.Requires(enclosingBlock != null);
      Contract.Requires(incarnationMap != null);
      Contract.Requires(oldFrameSubst != null);
      Contract.Requires(passiveCmds != null);
      Contract.Requires(mvInfo != null);

      AddDebugInfo(c, incarnationMap, passiveCmds, debugInfos);
      Substitution incarnationSubst = Substituter.SubstitutionFromDictionary(incarnationMap);

      Microsoft.Boogie.VCExprAST.QuantifierInstantiationEngine.SubstituteIncarnationInInstantiationSources(c, incarnationSubst);

      #region assert/assume P |--> assert/assume P[x := in(x)], out := in

      if (c is PredicateCmd)
      {
        Contract.Assert(c is AssertCmd || c is AssumeCmd); // otherwise, unexpected PredicateCmd type

        PredicateCmd pc = (PredicateCmd) c.Clone();
        Contract.Assert(pc != null);

        QKeyValue current = pc.Attributes;
        while (current != null)
        {
          if (current.Key == "minimize" || current.Key == "maximize")
          {
            Contract.Assume(current.Params.Count == 1);
            var param = current.Params[0] as Expr;
            Contract.Assume(param != null && (param.Type.IsInt || param.Type.IsReal || param.Type.IsBv));
            current.ClearParams();
            current.AddParam(Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, param));
          }

          if (current.Key == "verified_under")
          {
            Contract.Assume(current.Params.Count == 1);
            var param = current.Params[0] as Expr;
            Contract.Assume(param != null && param.Type.IsBool);
            current.ClearParams();
            current.AddParam(Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, param));
          }

          current = current.Next;
        }

        Expr copy = Substituter.ApplyReplacingOldExprs(incarnationSubst, oldFrameSubst, pc.Expr);
        if (Options.ExpectingModel && pc is AssumeCmd captureStateAssumeCmd)
        {
          string description = QKeyValue.FindStringAttribute(pc.Attributes, "captureState");
          if (description != null)
          {
            if (!mvInfo.BlockToCapturePointIndex.TryGetValue(enclosingBlock, out var points)) {
              points = new List<(AssumeCmd, ModelViewInfo.Mapping)>();
              mvInfo.BlockToCapturePointIndex[enclosingBlock] = points;
            }
            var mapping = new ModelViewInfo.Mapping(description, new Dictionary<Variable, Expr>(incarnationMap));
            points.Add((captureStateAssumeCmd, mapping));
          }
        }

        Contract.Assert(copy != null);
        var dropCmd = false;
        var relevantAssumpVars = currentImplementation != null
          ? currentImplementation.RelevantInjectedAssumptionVariables(incarnationMap)
          : new List<LocalVariable>();
        var relevantDoomedAssumpVars = currentImplementation != null
          ? currentImplementation.RelevantDoomedInjectedAssumptionVariables(incarnationMap)
          : new List<LocalVariable>();
        var checksum = pc.Checksum;
        if (pc is AssertCmd)
        {
          var ac = (AssertCmd) pc;
          ac.OrigExpr = ac.Expr;
          Contract.Assert(ac.IncarnationMap == null);
          ac.IncarnationMap = (Dictionary<Variable, Expr>) cce.NonNull(new Dictionary<Variable, Expr>(incarnationMap));

          var subsumption = Wlp.Subsumption(Options, ac);
          if (relevantDoomedAssumpVars.Any())
          {
            TraceCachingAction(traceWriter, pc, CachingAction.DoNothingToAssert);
          }
          else if (currentImplementation != null
                   && currentImplementation.HasCachedSnapshot
                   && checksum != null
                   && currentImplementation.IsAssertionChecksumInCachedSnapshot(checksum)
                   && !currentImplementation.IsErrorChecksumInCachedSnapshot(checksum))
          {
            if (!currentImplementation.AnyErrorsInCachedSnapshot
                && currentImplementation.InjectedAssumptionVariables.Count == 1
                && relevantAssumpVars.Count == 1)
            {
              TraceCachingAction(traceWriter, pc, CachingAction.MarkAsPartiallyVerified);
            }
            else
            {
              var assmVars = currentImplementation.ConjunctionOfInjectedAssumptionVariables(incarnationMap, out var isTrue);
              TraceCachingAction(traceWriter, pc,
                !isTrue ? CachingAction.MarkAsPartiallyVerified : CachingAction.MarkAsFullyVerified);
              var litExpr = ac.Expr as LiteralExpr;
              if (litExpr == null || !litExpr.IsTrue)
              {
                ac.MarkAsVerifiedUnder(assmVars);
              }
              else
              {
                dropCmd = true;
              }
            }
          }
          else if (currentImplementation != null
                   && currentImplementation.HasCachedSnapshot
                   && relevantAssumpVars.Count == 0
                   && checksum != null
                   && currentImplementation.IsAssertionChecksumInCachedSnapshot(checksum)
                   && currentImplementation.IsErrorChecksumInCachedSnapshot(checksum))
          {
            TraceCachingAction(traceWriter, pc, CachingAction.RecycleError);
            ac.MarkAsVerifiedUnder(Expr.True);
            currentImplementation.AddRecycledFailingAssertion(ac);
            pc.Attributes = new QKeyValue(Token.NoToken, "recycled_failing_assertion", new List<object>(),
              pc.Attributes);
          }
          else
          {
            TraceCachingAction(traceWriter, pc, CachingAction.DoNothingToAssert);
          }
        }
        else if (pc is AssumeCmd
                 && QKeyValue.FindBoolAttribute(pc.Attributes, "precondition_previous_snapshot")
                 && pc.SugaredCmdChecksum != null)
        {
          if (!relevantDoomedAssumpVars.Any()
              && currentImplementation.HasCachedSnapshot
              && currentImplementation.IsAssertionChecksumInCachedSnapshot(pc.SugaredCmdChecksum)
              && !currentImplementation.IsErrorChecksumInCachedSnapshot(pc.SugaredCmdChecksum))
          {
            var assmVars = currentImplementation.ConjunctionOfInjectedAssumptionVariables(incarnationMap, out var isTrue);
            if (!isTrue)
            {
              copy = LiteralExpr.Imp(assmVars, copy);
              TraceCachingAction(traceWriter, pc, CachingAction.MarkAsPartiallyVerified);
            }
            else
            {
              TraceCachingAction(traceWriter, pc, CachingAction.MarkAsFullyVerified);
            }
          }
          else
          {
            TraceCachingAction(traceWriter, pc, CachingAction.DropAssume);
            dropCmd = true;
          }
        }
        else if (pc is AssumeCmd && QKeyValue.FindBoolAttribute(pc.Attributes, "assumption_variable_initialization"))
        {
          var identExpr = pc.Expr as IdentifierExpr;
          if (identExpr != null && identExpr.Decl != null && !incarnationMap.ContainsKey(identExpr.Decl))
          {
            incarnationMap[identExpr.Decl] = LiteralExpr.True;
            dropCmd = true;
          }
        }

        pc.Expr = copy;
        if (!dropCmd)
        {
          passiveCmds.Add(pc);
        }
      }

      #endregion

      #region x1 := E1, x2 := E2, ... |--> assume x1' = E1[in] & x2' = E2[in], out := in( x |-> x' ) [except as noted below]

      else if (c is AssignCmd)
      {
        AssignCmd assign = ((AssignCmd) c).AsSimpleAssignCmd; // first remove map assignments
        Contract.Assert(assign != null);

        #region Substitute all variables in E with the current map

        List<Expr> copies = new List<Expr>();
        foreach (Expr e in assign.Rhss)
        {
          Contract.Assert(e != null);
          copies.Add(Substituter.ApplyReplacingOldExprs(incarnationSubst,
            oldFrameSubst,
            e));
        }

        #endregion

        List<Expr /*!>!*/> assumptions = new List<Expr>();
        // it might be too slow to create a new dictionary each time ...
        IDictionary<Variable, Expr> newIncarnationMappings =
          new Dictionary<Variable, Expr>();

        for (int i = 0; i < assign.Lhss.Count; ++i)
        {
          IdentifierExpr lhsIdExpr =
            cce.NonNull((SimpleAssignLhs) assign.Lhss[i]).AssignedVariable;
          Variable lhs = cce.NonNull(lhsIdExpr.Decl);
          Contract.Assert(lhs != null);
          Expr rhs = assign.Rhss[i];
          Contract.Assert(rhs != null);

          // don't create incarnations for assignments of literals or single variables.
          if (rhs is LiteralExpr)
          {
            incarnationMap[lhs] = rhs;
          }
          else if (rhs is IdentifierExpr)
          {
            IdentifierExpr ie = (IdentifierExpr) rhs;
            if (incarnationMap.ContainsKey(cce.NonNull(ie.Decl)))
            {
              newIncarnationMappings[lhs] = cce.NonNull((Expr) incarnationMap[ie.Decl]);
            }
            else
            {
              newIncarnationMappings[lhs] = ie;
            }
          }
          else
          {
            IdentifierExpr x_prime_exp = null;

            #region Make a new incarnation, x', for variable x, but only if x is *not* already an incarnation

            if (lhs is Incarnation)
            {
              // incarnations are already written only once, no need to make an incarnation of an incarnation
              x_prime_exp = lhsIdExpr;
            }
            else
            {
              Variable v = CreateIncarnation(lhs, c);
              x_prime_exp = new IdentifierExpr(lhsIdExpr.tok, v);
              newIncarnationMappings[lhs] = x_prime_exp;
            }

            #endregion

            var nAryExpr = copies[i] as NAryExpr;
            if (nAryExpr != null)
            {
              var binOp = nAryExpr.Fun as BinaryOperator;
              if (binOp != null
                  && binOp.Op == BinaryOperator.Opcode.And)
              {
                var arg0 = nAryExpr.Args[0] as LiteralExpr;
                var arg1 = nAryExpr.Args[1] as LiteralExpr;
                if ((arg0 != null && arg0.IsTrue) || (arg1 != null && arg1.IsFalse))
                {
                  // Replace the expressions "true && arg1" or "arg0 && false" by "arg1".
                  copies[i] = nAryExpr.Args[1];
                }
              }
            }

            #region Create an assume command with the new variable

            assumptions.Add(TypedExprEq(x_prime_exp, copies[i],
              x_prime_exp.Decl != null && x_prime_exp.Decl.Name.Contains("a##cached##")));

            #endregion
          }
        }

        foreach (KeyValuePair<Variable, Expr> pair in newIncarnationMappings)
        {
          Contract.Assert(pair.Key != null && pair.Value != null);
          incarnationMap[pair.Key] = pair.Value;
        }

        if (assumptions.Count > 0)
        {
          Expr assumption = assumptions[0];

          for (int i = 1; i < assumptions.Count; ++i)
          {
            Contract.Assert(assumption != null);
            assumption = Expr.And(assumption, assumptions[i]);
          }

          var assumeCmd = new AssumeCmd(c.tok, assumption);
          // Copy any {:id ...} from the assignment to the assumption, so
          // we can track it while analyzing verification coverage.
          (assumeCmd as ICarriesAttributes).CopyIdFrom(assign.tok, assign);
          passiveCmds.Add(assumeCmd);
        }

        if (currentImplementation != null
            && currentImplementation.HasCachedSnapshot
            && !currentImplementation.AnyErrorsInCachedSnapshot
            && currentImplementation.DoomedInjectedAssumptionVariables.Count == 0
            && currentImplementation.InjectedAssumptionVariables.Count == 1
            && assign.Lhss.Count == 1)
        {
          var identExpr = assign.Lhss[0].AsExpr as IdentifierExpr;
          if (identExpr != null && identExpr.Decl != null &&
              QKeyValue.FindBoolAttribute(identExpr.Decl.Attributes, "assumption") &&
              incarnationMap.TryGetValue(identExpr.Decl, out var incarnation))
          {
            TraceCachingAction(traceWriter, assign, CachingAction.AssumeNegationOfAssumptionVariable);
            passiveCmds.Add(new AssumeCmd(c.tok, Expr.Not(incarnation)));
          }
        }
      }

      #endregion

      #region havoc w |--> assume whereClauses, out := in( w |-> w' )

      else if (c is HavocCmd)
      {
        if (this.preHavocIncarnationMap == null
        ) // Save a copy of the incarnation map (at the top of a sequence of havoc statements)
        {
          this.preHavocIncarnationMap = new Dictionary<Variable, Expr>(incarnationMap);
        }

        HavocCmd hc = (HavocCmd) c;
        Contract.Assert(c != null);
        // If an assumption variable for postconditions is included here, it must have been assigned within a loop.
        // We do not need to havoc it if we have performed a modular proof of the loop (i.e., using only the loop
        // invariant) in the previous snapshot and, consequently, the corresponding assumption did not affect the
        // anything after the loop. We can achieve this by simply not updating/adding it in the incarnation map.
        List<IdentifierExpr> havocVars = hc.Vars.Where(v =>
            !(QKeyValue.FindBoolAttribute(v.Decl.Attributes, "assumption") && v.Decl.Name.StartsWith("a##cached##")))
          .ToList();
        // First, compute the new incarnations
        foreach (IdentifierExpr ie in havocVars)
        {
          Contract.Assert(ie != null);
          if (!(ie.Decl is Incarnation))
          {
            Variable x = cce.NonNull(ie.Decl);
            Variable x_prime = CreateIncarnation(x, c);
            incarnationMap[x] = new IdentifierExpr(x_prime.tok, x_prime);
          }
        }

        // Then, perform the assume of the where clauses, using the updated incarnations
        Substitution updatedIncarnationSubst = Substituter.SubstitutionFromDictionary(incarnationMap);
        foreach (IdentifierExpr ie in havocVars)
        {
          Contract.Assert(ie != null);
          if (!(ie.Decl is Incarnation))
          {
            Variable x = cce.NonNull(ie.Decl);
            Expr w = x.TypedIdent.WhereExpr;
            if (w != null)
            {
              Expr copy = Substituter.ApplyReplacingOldExprs(updatedIncarnationSubst, oldFrameSubst, w);
              passiveCmds.Add(new AssumeCmd(c.tok, copy));
            }
          }
        }

        // Add the following assume-statement for each assumption variable 'v', where 'v_post' is the new incarnation and 'v_pre' is the old one:
        // assume v_post ==> v_pre;
        foreach (IdentifierExpr ie in havocVars)
        {
          if (QKeyValue.FindBoolAttribute(ie.Decl.Attributes, "assumption"))
          {
            var preInc = (Expr) (preHavocIncarnationMap[ie.Decl].Clone());
            var postInc = (Expr) (incarnationMap[ie.Decl].Clone());
            passiveCmds.Add(new AssumeCmd(c.tok, Expr.Imp(postInc, preInc)));
          }
        }
      }

      #endregion

      else if (c is CommentCmd)
      {
        // comments are just for debugging and don't affect verification
      } else if (c is HideRevealCmd)
      {
        passiveCmds.Add(c);
      } else if (c is ChangeScope)
      {
        passiveCmds.Add(c);
      }
      else if (c is SugaredCmd sug)
      {
        Cmd cmd = sug.GetDesugaring(Options);
        Contract.Assert(cmd != null);
        TurnIntoPassiveCmd(traceWriter, cmd, enclosingBlock, incarnationMap, oldFrameSubst, passiveCmds, mvInfo, debugInfos);
      }
      else if (c is StateCmd st)
      {
        this.preHavocIncarnationMap = null; // we do not need to remember the previous incarnations

        // account for any where clauses among the local variables
        foreach (Variable v in st.Locals)
        {
          Contract.Assert(v != null);
          Expr w = v.TypedIdent.WhereExpr;
          if (w != null)
          {
            passiveCmds.Add(new AssumeCmd(v.tok, w));
          }
        }

        // do the sub-commands
        foreach (Cmd s in st.Cmds)
        {
          Contract.Assert(s != null);
          TurnIntoPassiveCmd(traceWriter, s, enclosingBlock, incarnationMap, oldFrameSubst, passiveCmds, mvInfo, debugInfos);
        }

        // remove the local variables from the incarnation map
        foreach (Variable v in st.Locals)
        {
          Contract.Assert(v != null);
          incarnationMap.Remove(v);
        }
      }

      #region There shouldn't be any other types of commands at this point

      else
      {
        Debug.Fail(
          "Internal Error: Passive transformation handed a command that is not one of assert,assume,havoc,assign.");
      }

      #endregion


      #region We remember if we have put an havoc statement into a passive form

      if (!(c is HavocCmd))
      {
        this.preHavocIncarnationMap = null;
      }
      // else: it has already been set by the case for the HavocCmd

      #endregion
    }

    NAryExpr TypedExprEq(Expr e0, Expr e1, bool doNotResolveOverloading = false)
    {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      NAryExpr e = Expr.Eq(e0, e1);
      var fun = e.Fun as IOverloadedAppliable;
      if (fun != null)
      {
        fun.DoNotResolveOverloading = doNotResolveOverloading;
      }

      e.Type = Microsoft.Boogie.Type.Bool;
      e.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      return e;
    }

    /// <summary>
    /// Creates a new block to add to impl.Blocks, where impl is the implementation that contains
    /// succ.  Caller must do the add to impl.Blocks.
    /// </summary>
    protected Block CreateBlockBetween(int predIndex, Block succ)
    {
      Contract.Requires(0 <= predIndex && predIndex < succ.Predecessors.Count);


      Contract.Requires(succ != null);
      Contract.Ensures(Contract.Result<Block>() != null);

      Block pred = cce.NonNull(succ.Predecessors[predIndex]);

      string newBlockLabel = pred.Label + "_@2_" + succ.Label;

      // successor of newBlock list
      List<String> ls = new List<String>();
      ls.Add(succ.Label);
      List<Block> bs = new List<Block>();
      bs.Add(succ);

      Block newBlock = new Block(
        new Token(-17, -4),
        newBlockLabel,
        new List<Cmd>(),
        new GotoCmd(Token.NoToken, ls, bs)
      );

      // predecessors of newBlock
      List<Block> ps = new List<Block>();
      ps.Add(pred);
      newBlock.Predecessors = ps;

      // fix successors of pred

      #region Change the edge "pred->succ" to "pred->newBlock"

      GotoCmd gtc = (GotoCmd) cce.NonNull(pred.TransferCmd);
      Contract.Assume(gtc.labelTargets != null);
      Contract.Assume(gtc.labelNames != null);
      for (int i = 0, n = gtc.labelTargets.Count; i < n; i++)
      {
        if (gtc.labelTargets[i] == succ)
        {
          gtc.labelTargets[i] = newBlock;
          gtc.labelNames[i] = newBlockLabel;
          break;
        }
      }

      #endregion Change the edge "pred->succ" to "pred->newBlock"

      // fix predecessors of succ
      succ.Predecessors[predIndex] = newBlock;

      return newBlock;
    }

    protected void AddBlocksBetween(List<Block> blocks)
    {
      Contract.Requires(blocks != null);

      #region Introduce empty blocks between join points and their multi-successor predecessors

      List<Block> tweens = new List<Block>();
      foreach (Block b in blocks)
      {
        int nPreds = b.Predecessors.Count;
        if (nPreds > 1)
        {
          // b is a join point (i.e., it has more than one predecessor)
          for (int i = 0; i < nPreds; i++)
          {
            GotoCmd gotocmd = (GotoCmd) (cce.NonNull(b.Predecessors[i]).TransferCmd);
            if (gotocmd.labelNames != null && gotocmd.labelNames.Count > 1)
            {
              tweens.Add(CreateBlockBetween(i, b));
            }
          }
        }
      }

      blocks.AddRange(tweens); // must wait until iteration is done before changing the list

      #endregion
    }


    public void Dispose()
    {
      Dispose(true);
      GC.SuppressFinalize(this);
    }

    protected virtual void Dispose(bool disposing)
    {
      if (!_disposed)
      {
        if (disposing)
        {
          Close();
        }

        _disposed = true;
      }
    }
  }

  public enum VcOutcome
  {
    Correct,
    Errors,
    TimedOut,
    OutOfResource,
    OutOfMemory,
    Inconclusive,
    ReachedBound,
    SolverException
  }

  public record ImplementationRun(Implementation Implementation, TextWriter OutputWriter) {

  }
}
