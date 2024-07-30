using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.IO;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.SMTLib;
using System.Threading.Tasks;
using VCGeneration;

namespace VC
{
  public class Split : ProofRun
  {
      public VCGenOptions Options { get; }
      private readonly Random randomGen;
      public ImplementationRun Run { get; }

      public int RandomSeed { get; }

      public List<Block> Blocks { get; set; }
      readonly List<Block> bigBlocks = new();
      public List<AssertCmd> Asserts => Blocks.SelectMany(block => block.cmds.OfType<AssertCmd>()).ToList();
      public readonly IReadOnlyList<Declaration> TopLevelDeclarations;
      public IReadOnlyList<Declaration> prunedDeclarations;
      
      public IReadOnlyList<Declaration> PrunedDeclarations {
        get {
          if (prunedDeclarations == null) {
            prunedDeclarations = Pruner.GetLiveDeclarations(parent.Options, parent.program, Blocks).ToList();
          }

          return prunedDeclarations;
        }
      }

      readonly Dictionary<Block /*!*/, BlockStats /*!*/> /*!*/
        stats = new Dictionary<Block /*!*/, BlockStats /*!*/>();

      static int currentId = -1;

      Block splitBlock;
      bool assertToAssume;

      List<Block /*!*/> /*!*/
        assumizedBranches = new List<Block /*!*/>();

      double score;
      bool scoreComputed;
      double totalCost;
      int assertionCount;
      double assertionCost; // without multiplication by paths

      public Dictionary<TransferCmd, ReturnCmd> GotoCmdOrigins { get; }

      public readonly VerificationConditionGenerator /*!*/
        parent;

      public Implementation /*!*/ Implementation => Run.Implementation;

      Dictionary<Block /*!*/, Block /*!*/> /*!*/
        copies = new Dictionary<Block /*!*/, Block /*!*/>();

      bool doingSlice;
      double sliceInitialLimit;
      double sliceLimit;
      bool slicePos;

      HashSet<Block /*!*/> /*!*/ protectedFromAssertToAssume = new HashSet<Block /*!*/>();

      HashSet<Block /*!*/> /*!*/ keepAtAll = new HashSet<Block /*!*/>();

      // async interface
      public int SplitIndex { get; set; }
      public VerificationConditionGenerator.ErrorReporter reporter;

      public Split(VCGenOptions options, List<Block /*!*/> /*!*/ blocks,
        Dictionary<TransferCmd, ReturnCmd> /*!*/ gotoCmdOrigins,
        VerificationConditionGenerator /*!*/ par, ImplementationRun run, int? randomSeed = null)
      {
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(par != null);
        this.Blocks = blocks;
        this.GotoCmdOrigins = gotoCmdOrigins;
        parent = par;
        this.Run = run;
        this.Options = options;
        Interlocked.Increment(ref currentId);

        TopLevelDeclarations = par.program.TopLevelDeclarations;
        RandomSeed = randomSeed ?? Implementation.RandomSeed ?? Options.RandomSeed ?? 0;
        randomGen = new Random(RandomSeed);
      }
      
      

      public void PrintSplit() {
        if (Options.PrintSplitFile == null) {
          return;
        }

        using var writer = new TokenTextWriter(
          $"{Options.PrintSplitFile}-{Util.EscapeFilename(Implementation.Name)}-{SplitIndex}.spl", false,
          Options.PrettyPrint, Options);

        Implementation.EmitImplementation(writer, 0, Blocks, false);
        PrintSplitDeclarations(writer);
      }

      private void PrintSplitDeclarations(TokenTextWriter writer)
      {
        if (!Options.Prune || !Options.PrintSplitDeclarations)
        {
          return;
        }

        var functionAxioms =
          PrunedDeclarations.OfType<Function>().Where(f => f.DefinitionAxioms.Any()).SelectMany(f => f.DefinitionAxioms);
        var constantAxioms =
          PrunedDeclarations.OfType<Constant>().Where(f => f.DefinitionAxioms.Any()).SelectMany(c => c.DefinitionAxioms);

        foreach (var declaration in PrunedDeclarations.Except(functionAxioms.Concat(constantAxioms)).ToList())
        {
          declaration.Emit(writer, 0);
        }

        writer.Close();
      }

      public double Cost
      {
        get
        {
          ComputeBestSplit();
          return totalCost;
        }
      }

      public bool LastChance
      {
        get
        {
          ComputeBestSplit();
          return assertionCount == 1 && score < 0;
        }
      }

      public string Stats
      {
        get
        {
          ComputeBestSplit();
          return $"(cost:{totalCost:0}/{assertionCost:0}{(LastChance ? " last" : "")})";
        }
      }

      public void DumpDot(int splitNum)
      {
        using (StreamWriter sw = File.CreateText($"{Implementation.Name}.split.{splitNum}.dot"))
        {
          sw.WriteLine("digraph G {");

          ComputeBestSplit();
          List<Block> saved = assumizedBranches;
          Contract.Assert(saved != null);
          assumizedBranches = new List<Block>();
          DoComputeScore(false);
          assumizedBranches = saved;

          foreach (Block b in bigBlocks)
          {
            Contract.Assert(b != null);
            BlockStats s = GetBlockStats(b);
            foreach (Block t in s.virtualSuccessors)
            {
              Contract.Assert(t != null);
              sw.WriteLine("n{0} -> n{1};", s.id, GetBlockStats(t).id);
            }

            sw.WriteLine("n{0} [label=\"{1}:\\n({2:0.0}+{3:0.0})*{4:0.0}\"{5}];",
              s.id, b.Label,
              s.assertionCost, s.assumptionCost, s.incomingPaths,
              s.assertionCost > 0 ? ",shape=box" : "");
          }

          sw.WriteLine("}");
          sw.Close();
        }

        string filename = string.Format("{0}.split.{1}.bpl", Implementation.Name, splitNum);
        using (StreamWriter sw = File.CreateText(filename))
        {
          int oldPrintUnstructured = Options.PrintUnstructured;
          Options.PrintUnstructured = 2; // print only the unstructured program
          bool oldPrintDesugaringSetting = Options.PrintDesugarings;
          Options.PrintDesugarings = false;
          List<Block> backup = Implementation.Blocks;
          Contract.Assert(backup != null);
          Implementation.Blocks = Blocks;
          Implementation.Emit(new TokenTextWriter(filename, sw, /*setTokens=*/ false, /*pretty=*/ false, Options), 0);
          Implementation.Blocks = backup;
          Options.PrintDesugarings = oldPrintDesugaringSetting;
          Options.PrintUnstructured = oldPrintUnstructured;
        }
      }

      int bsid;

      BlockStats GetBlockStats(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<BlockStats>() != null);

        if (!stats.TryGetValue(b, out var s))
        {
          s = new BlockStats(b, bsid++);
          stats[b] = s;
        }

        return cce.NonNull(s);
      }

      double AssertionCost(PredicateCmd c)
      {
        return 1.0;
      }

      void CountAssertions(Block b)
      {
        Contract.Requires(b != null);
        BlockStats s = GetBlockStats(b);
        if (s.assertionCost >= 0)
        {
          return; // already done
        }

        s.bigBlock = true;
        s.assertionCost = 0;
        s.assumptionCost = 0;
        foreach (Cmd c in b.Cmds)
        {
          if (c is AssertCmd)
          {
            double cost = AssertionCost((AssertCmd)c);
            s.assertionCost += cost;
            assertionCount++;
            assertionCost += cost;
          }
          else if (c is AssumeCmd)
          {
            s.assumptionCost += AssertionCost((AssumeCmd)c);
          }
        }

        foreach (Block c in b.Exits())
        {
          Contract.Assert(c != null);
          s.virtualSuccessors.Add(c);
        }

        if (s.virtualSuccessors.Count == 1)
        {
          Block next = s.virtualSuccessors[0];
          BlockStats se = GetBlockStats(next);
          CountAssertions(next);
          if (next.Predecessors.Count > 1 || se.virtualSuccessors.Count != 1)
          {
            return;
          }

          s.virtualSuccessors[0] = se.virtualSuccessors[0];
          s.assertionCost += se.assertionCost;
          s.assumptionCost += se.assumptionCost;
          se.bigBlock = false;
        }
      }

      HashSet<Block /*!*/> /*!*/ ComputeReachableNodes(Block /*!*/ b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(cce.NonNull(Contract.Result<HashSet<Block /*!*/>>()));
        BlockStats s = GetBlockStats(b);
        if (s.reachableBlocks != null)
        {
          return s.reachableBlocks;
        }

        HashSet<Block /*!*/> blocks = new HashSet<Block /*!*/>();
        s.reachableBlocks = blocks;
        blocks.Add(b);
        foreach (Block /*!*/ succ in b.Exits())
        {
          Contract.Assert(succ != null);
          foreach (Block r in ComputeReachableNodes(succ))
          {
            Contract.Assert(r != null);
            blocks.Add(r);
          }
        }

        return blocks;
      }

      double ProverCost(double vcCost)
      {
        return vcCost * vcCost;
      }

      void ComputeBestSplit()
      {
        if (scoreComputed)
        {
          return;
        }

        scoreComputed = true;

        assertionCount = 0;

        foreach (Block b in Blocks)
        {
          Contract.Assert(b != null);
          CountAssertions(b);
        }

        foreach (Block b in Blocks)
        {
          Contract.Assert(b != null);
          BlockStats bs = GetBlockStats(b);
          if (bs.bigBlock)
          {
            bigBlocks.Add(b);
            foreach (Block ch in bs.virtualSuccessors)
            {
              Contract.Assert(ch != null);
              BlockStats chs = GetBlockStats(ch);
              if (!chs.bigBlock)
              {
                Options.OutputWriter.WriteLine("non-big {0} accessed from {1}", ch, b);
                DumpDot(-1);
                Contract.Assert(false);
                throw new cce.UnreachableException();
              }

              chs.virtualPredecessors.Add(b);
            }
          }
        }

        assumizedBranches.Clear();
        totalCost = ProverCost(DoComputeScore(false));

        score = double.PositiveInfinity;
        Block bestSplit = null;
        List<Block> savedBranches = new List<Block>();

        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          GotoCmd gt = b.TransferCmd as GotoCmd;
          if (gt == null)
          {
            continue;
          }

          List<Block> targ = cce.NonNull(gt.labelTargets);
          if (targ.Count < 2)
          {
            continue;
          }
          // caution, we only consider two first exits

          double left0, right0, left1, right1;
          splitBlock = b;

          assumizedBranches.Clear();
          assumizedBranches.Add(cce.NonNull(targ[0]));
          left0 = DoComputeScore(true);
          right0 = DoComputeScore(false);

          assumizedBranches.Clear();
          for (int idx = 1; idx < targ.Count; idx++)
          {
            assumizedBranches.Add(cce.NonNull(targ[idx]));
          }

          left1 = DoComputeScore(true);
          right1 = DoComputeScore(false);

          double currentScore = ProverCost(left1) + ProverCost(right1);
          double otherScore = ProverCost(left0) + ProverCost(right0);

          if (otherScore < currentScore)
          {
            currentScore = otherScore;
            assumizedBranches.Clear();
            assumizedBranches.Add(cce.NonNull(targ[0]));
          }

          if (currentScore < score)
          {
            score = currentScore;
            bestSplit = splitBlock;
            savedBranches.Clear();
            savedBranches.AddRange(assumizedBranches);
          }
        }

        if (Options.VcsPathSplitMult * score > totalCost)
        {
          splitBlock = null;
          score = -1;
        }
        else
        {
          assumizedBranches = savedBranches;
          splitBlock = bestSplit;
        }
      }

      void UpdateIncomingPaths(BlockStats s)
      {
        Contract.Requires(s != null);
        if (s.incomingPaths < 0.0)
        {
          int count = 0;
          s.incomingPaths = 0.0;
          if (!keepAtAll.Contains(s.block))
          {
            return;
          }

          foreach (Block b in s.virtualPredecessors)
          {
            Contract.Assert(b != null);
            BlockStats ch = GetBlockStats(b);
            Contract.Assert(ch != null);
            UpdateIncomingPaths(ch);
            if (ch.incomingPaths > 0.0)
            {
              s.incomingPaths += ch.incomingPaths;
              count++;
            }
          }

          if (count > 1)
          {
            s.incomingPaths *= Options.VcsPathJoinMult;
          }
        }
      }

      void ComputeBlockSetsHelper(Block b, bool allowSmall)
      {
        Contract.Requires(b != null);
        if (keepAtAll.Contains(b))
        {
          return;
        }

        keepAtAll.Add(b);

        if (allowSmall)
        {
          foreach (Block ch in b.Exits())
          {
            Contract.Assert(ch != null);
            if (b == splitBlock && assumizedBranches.Contains(ch))
            {
              continue;
            }

            ComputeBlockSetsHelper(ch, allowSmall);
          }
        }
        else
        {
          foreach (Block ch in GetBlockStats(b).virtualSuccessors)
          {
            Contract.Assert(ch != null);
            if (b == splitBlock && assumizedBranches.Contains(ch))
            {
              continue;
            }

            ComputeBlockSetsHelper(ch, allowSmall);
          }
        }
      }

      void ComputeBlockSets(bool allowSmall)
      {
        protectedFromAssertToAssume.Clear();
        keepAtAll.Clear();

        Debug.Assert(splitBlock == null || GetBlockStats(splitBlock).bigBlock);
        Debug.Assert(GetBlockStats(Blocks[0]).bigBlock);

        if (assertToAssume)
        {
          foreach (Block b in allowSmall ? Blocks : bigBlocks)
          {
            Contract.Assert(b != null);
            if (ComputeReachableNodes(b).Contains(cce.NonNull(splitBlock)))
            {
              keepAtAll.Add(b);
            }
          }

          foreach (Block b in assumizedBranches)
          {
            Contract.Assert(b != null);
            foreach (Block r in ComputeReachableNodes(b))
            {
              Contract.Assert(r != null);
              if (allowSmall || GetBlockStats(r).bigBlock)
              {
                keepAtAll.Add(r);
                protectedFromAssertToAssume.Add(r);
              }
            }
          }
        }
        else
        {
          ComputeBlockSetsHelper(Blocks[0], allowSmall);
        }
      }

      bool ShouldAssumize(Block b)
      {
        Contract.Requires(b != null);
        return assertToAssume && !protectedFromAssertToAssume.Contains(b);
      }

      double DoComputeScore(bool aa)
      {
        assertToAssume = aa;
        ComputeBlockSets(false);

        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          GetBlockStats(b).incomingPaths = -1.0;
        }

        GetBlockStats(Blocks[0]).incomingPaths = 1.0;

        double cost = 0.0;
        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          if (keepAtAll.Contains(b))
          {
            BlockStats s = GetBlockStats(b);
            UpdateIncomingPaths(s);
            double local = s.assertionCost;
            if (ShouldAssumize(b))
            {
              local = (s.assertionCost + s.assumptionCost) * Options.VcsAssumeMult;
            }
            else
            {
              local = s.assumptionCost * Options.VcsAssumeMult + s.assertionCost;
            }

            local = local + local * s.incomingPaths * Options.VcsPathCostMult;
            cost += local;
          }
        }

        return cost;
      }

      List<Cmd> SliceCmds(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);

        List<Cmd> seq = b.Cmds;
        Contract.Assert(seq != null);
        if (!doingSlice && !ShouldAssumize(b))
        {
          return seq;
        }

        List<Cmd> res = new List<Cmd>();
        foreach (Cmd c in seq)
        {
          Contract.Assert(c != null);
          AssertCmd a = c as AssertCmd;
          Cmd theNewCmd = c;
          bool swap = false;
          if (a != null)
          {
            if (doingSlice)
            {
              double cost = AssertionCost(a);
              bool first = (sliceLimit - cost) >= 0 || sliceInitialLimit == sliceLimit;
              sliceLimit -= cost;
              swap = slicePos == first;
            }
            else if (assertToAssume)
            {
              swap = true;
            }
            else
            {
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }

            if (swap)
            {
              theNewCmd = VerificationConditionGenerator.AssertTurnedIntoAssume(Options, a);
            }
          }

          res.Add(theNewCmd);
        }

        return res;
      }

      Block CloneBlock(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        if (copies.TryGetValue(b, out var res))
        {
          return cce.NonNull(res);
        }

        res = new Block(b.tok, b.Label, SliceCmds(b), b.TransferCmd);
        GotoCmd gt = b.TransferCmd as GotoCmd;
        copies[b] = res;
        if (gt != null)
        {
          GotoCmd newGoto = new GotoCmd(gt.tok, new List<String>(), new List<Block>());
          res.TransferCmd = newGoto;
          int pos = 0;
          foreach (Block ch in cce.NonNull(gt.labelTargets))
          {
            Contract.Assert(ch != null);
            Contract.Assert(doingSlice ||
                            (assertToAssume || (keepAtAll.Contains(ch) || assumizedBranches.Contains(ch))));
            if (doingSlice ||
                ((b != splitBlock || assumizedBranches.Contains(ch) == assertToAssume) &&
                 keepAtAll.Contains(ch)))
            {
              newGoto.AddTarget(CloneBlock(ch));
            }

            pos++;
          }
        }

        return res;
      }

      private Split DoSplit()
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        copies.Clear();
        CloneBlock(Blocks[0]);
        var newBlocks = new List<Block>();
        var newGotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
        foreach (var block in Blocks)
        {
          Contract.Assert(block != null);
          if (!copies.TryGetValue(block, out var tmp))
          {
            continue;
          }

          newBlocks.Add(cce.NonNull(tmp));
          if (GotoCmdOrigins.TryGetValue(block.TransferCmd, out var origin))
          {
            newGotoCmdOrigins[tmp.TransferCmd] = origin;
          }

          foreach (var predecessor in block.Predecessors)
          {
            Contract.Assert(predecessor != null);
            if (copies.TryGetValue(predecessor, out var tmp2))
            {
              tmp.Predecessors.Add(tmp2);
            }
          }
        }

        return new Split(Options, newBlocks, newGotoCmdOrigins, parent, Run);
      }

      private Split SplitAt(int idx)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        assertToAssume = idx == 0;
        doingSlice = false;
        ComputeBlockSets(true);

        return DoSplit();
      }

      private Split SliceAsserts(double limit, bool pos)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        slicePos = pos;
        sliceLimit = limit;
        sliceInitialLimit = limit;
        doingSlice = true;
        Split r = DoSplit();
        /*
        Console.WriteLine("split {0} / {1} -->", limit, pos);
        List<Block!> tmp = impl.Blocks;
        impl.Blocks = r.blocks;
        EmitImpl(impl, false);
        impl.Blocks = tmp;
        */

        return r;
      }

      void Print()
      {
        ConditionGeneration.EmitImpl(Options, Run, false, Blocks);
      }

      public Counterexample ToCounterexample(ProverContext context)
      {
        Contract.Requires(context != null);
        Contract.Ensures(Contract.Result<Counterexample>() != null);

        List<Block> trace = new List<Block>();
        foreach (Block block in Blocks)
        {
          Contract.Assert(block != null);
          trace.Add(block);
        }

        foreach (Block block in Blocks)
        {
          Contract.Assert(block != null);
          foreach (Cmd command in block.Cmds)
          {
            if (command is AssertCmd assertCmd)
            {
              var counterexample = VerificationConditionGenerator.AssertCmdToCounterexample(Options, assertCmd,
                cce.NonNull(block.TransferCmd), trace, null, null, null, context, this);
              Counterexamples.Add(counterexample);
              return counterexample;
            }
          }
        }

        Contract.Assume(false);
        throw new cce.UnreachableException();
      }

      public static List<Split /*!*/> /*!*/ DoSplit(Split initial, double splitThreshold, int maxSplits)
      {
        Contract.Requires(initial != null);
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Split>>()));

        var run = initial.Run;
        var result = new List<Split> { initial };

        while (result.Count < maxSplits)
        {
          Split best = null;
          int bestIndex = 0;
          for (var index = 0; index < result.Count; index++)
          {
            var split = result[index];
            Contract.Assert(split != null);
            split.ComputeBestSplit(); // TODO check totalCost first
            if (split.totalCost > splitThreshold &&
                (best == null || best.totalCost < split.totalCost) &&
                (split.assertionCount > 1 || split.splitBlock != null))
            {
              best = split;
              bestIndex = index;
            }
          }

          if (best == null)
          {
            break; // no split found
          }

          Split s0, s1;

          bool splitStats = initial.Options.TraceVerify;

          if (splitStats)
          {
            run.OutputWriter.WriteLine("{0} {1} -->",
              best.splitBlock == null ? "SLICE" : ("SPLIT@" + best.splitBlock.Label),
              best.Stats);
            if (best.splitBlock != null)
            {
              GotoCmd g = best.splitBlock.TransferCmd as GotoCmd;
              if (g != null)
              {
                run.OutputWriter.Write("    exits: ");
                foreach (Block b in cce.NonNull(g.labelTargets))
                {
                  Contract.Assert(b != null);
                  run.OutputWriter.Write("{0} ", b.Label);
                }

                run.OutputWriter.WriteLine("");
                run.OutputWriter.Write("    assumized: ");
                foreach (Block b in best.assumizedBranches)
                {
                  Contract.Assert(b != null);
                  run.OutputWriter.Write("{0} ", b.Label);
                }

                run.OutputWriter.WriteLine("");
              }
            }
          }

          if (best.splitBlock != null)
          {
            s0 = best.SplitAt(0);
            s1 = best.SplitAt(1);
          }
          else
          {
            best.splitBlock = null;
            s0 = best.SliceAsserts(best.assertionCost / 2, true);
            s1 = best.SliceAsserts(best.assertionCost / 2, false);
          }

          if (true)
          {
            var ss = new List<Block>
            {
              s0.Blocks[0],
              s1.Blocks[0]
            };
            try
            {
              best.SoundnessCheck(new HashSet<List<Block>>(new BlockListComparer()), best.Blocks[0], ss);
            }
            catch (Exception e)
            {
              run.OutputWriter.WriteLine(e);
              best.DumpDot(-1);
              s0.DumpDot(-2);
              s1.DumpDot(-3);
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }
          }

          if (splitStats)
          {
            s0.ComputeBestSplit();
            s1.ComputeBestSplit();
            run.OutputWriter.WriteLine("    --> {0}", s0.Stats);
            run.OutputWriter.WriteLine("    --> {0}", s1.Stats);
          }

          if (initial.Options.TraceVerify)
          {
            best.Print();
          }

          result[bestIndex] = s0;
          result.Add(s1);
        }

        return result;
      }

      public VerificationRunResult ReadOutcome(int iteration, Checker checker, VerifierCallback callback)
      {
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        SolverOutcome outcome = cce.NonNull(checker).ReadOutcome();

        if (Options.Trace && SplitIndex >= 0)
        {
          Run.OutputWriter.WriteLine("      --> split #{0} done,  [{1} s] {2}", SplitIndex + 1,
            checker.ProverRunTime.TotalSeconds, outcome);
        }

        if (Options.Trace && Options.TrackVerificationCoverage)
        {
          Run.OutputWriter.WriteLine("Proof dependencies:\n  {0}",
            string.Join("\n  ", CoveredElements.Select(s => s.Description).OrderBy(s => s)));
        }

        var resourceCount = checker.GetProverResourceCount();
        var result = new VerificationRunResult(
          VcNum: SplitIndex + 1,
          Iteration: iteration,
          StartTime: checker.ProverStart,
          Outcome: outcome,
          RunTime: checker.ProverRunTime,
          MaxCounterExamples: checker.Options.ErrorLimit,
          CounterExamples: Counterexamples,
          Asserts: Asserts,
          CoveredElements: CoveredElements,
          ResourceCount: resourceCount,
          SolverUsed: (Options as SMTLibSolverOptions)?.Solver);
        callback.OnVCResult(result);

        if (Options.VcsDumpSplits)
        {
          DumpDot(SplitIndex);
        }

        return result;
      }

      public List<Counterexample> Counterexamples { get; } = new();

      public HashSet<TrackedNodeComponent> CoveredElements { get; } = new();

      /// <summary>
      /// As a side effect, updates "this.parent.CumulativeAssertionCount".
      /// </summary>
      public async Task BeginCheck(TextWriter traceWriter, Checker checker, VerifierCallback callback,
        ModelViewInfo mvInfo, uint timeout,
        uint rlimit, CancellationToken cancellationToken)
      {
        PrintSplit();
        Contract.Requires(checker != null);
        Contract.Requires(callback != null);

        VCExpr vc;
        // Lock impl since we're setting impl.Blocks that is used to generate the VC.
        lock (Implementation)
        {
          Implementation.Blocks = Blocks;

          var absyIds = new ControlFlowIdMap<Absy>();

          ProverContext ctx = checker.TheoremProver.Context;
          Boogie2VCExprTranslator bet = ctx.BoogieExprTranslator;
          var cc = new VerificationConditionGenerator.CodeExprConversionClosure(traceWriter, checker.Pool.Options,
            absyIds, ctx);
          bet.SetCodeExprConverter(cc.CodeExprToVerificationCondition);

          var exprGen = ctx.ExprGen;
          VCExpr controlFlowVariableExpr = exprGen.Integer(BigNum.ZERO);
          vc = parent.GenerateVCAux(Implementation, controlFlowVariableExpr, absyIds, checker.TheoremProver.Context);
          Contract.Assert(vc != null);

          vc = QuantifierInstantiationEngine.Instantiate(Implementation, exprGen, bet, vc);

          VCExpr controlFlowFunctionAppl =
            exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
          VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl,
            exprGen.Integer(BigNum.FromInt(absyIds.GetId(Implementation.Blocks[0]))));
          vc = exprGen.Implies(eqExpr, vc);
          reporter = new VerificationConditionGenerator.ErrorReporter(Options, GotoCmdOrigins, absyIds,
            Implementation.Blocks, Implementation.debugInfos, callback,
            mvInfo, checker.TheoremProver.Context, parent.program, this);
        }

        if (Options.TraceVerify && SplitIndex >= 0)
        {
          Run.OutputWriter.WriteLine("-- after split #{0}", SplitIndex);
          Print();
        }

        checker.TheoremProver.SetAdditionalSmtOptions(Implementation.GetExtraSMTOptions()
          .Select(kv => new OptionValue(kv.Key, kv.Value)));
        await checker.BeginCheck(Description, vc, reporter, timeout, rlimit, cancellationToken);
      }

      public string Description
      {
        get
        {
          string description = cce.NonNull(Implementation.Name);
          if (SplitIndex >= 0)
          {
            description += "_split" + SplitIndex;
          }

          return description;
        }
      }

      private void SoundnessCheck(HashSet<List<Block> /*!*/> /*!*/ cache, Block /*!*/ orig,
        List<Block /*!*/> /*!*/ copies)
      {
        Contract.Requires(cce.NonNull(cache));
        Contract.Requires(orig != null);
        Contract.Requires(copies != null);
        {
          var t = new List<Block> { orig };
          foreach (Block b in copies)
          {
            Contract.Assert(b != null);
            t.Add(b);
          }

          if (cache.Contains(t))
          {
            return;
          }

          cache.Add(t);
        }

        for (int i = 0; i < orig.Cmds.Count; ++i)
        {
          Cmd cmd = orig.Cmds[i];
          if (cmd is AssertCmd)
          {
            int found = 0;
            foreach (Block c in copies)
            {
              Contract.Assert(c != null);
              if (c.Cmds[i] == cmd)
              {
                found++;
              }
            }

            if (found == 0)
            {
              throw new Exception(string.Format("missing assertion: {0}({1})", cmd.tok.filename, cmd.tok.line));
            }
          }
        }

        foreach (Block exit in orig.Exits())
        {
          Contract.Assert(exit != null);
          List<Block> newcopies = new List<Block>();
          foreach (Block c in copies)
          {
            foreach (Block cexit in c.Exits())
            {
              Contract.Assert(cexit != null);
              if (cexit.Label == exit.Label)
              {
                newcopies.Add(cexit);
              }
            }
          }

          if (newcopies.Count == 0)
          {
            throw new Exception("missing exit " + exit.Label);
          }

          SoundnessCheck(cache, exit, newcopies);
        }
      }

      public int NextRandom()
      {
        return randomGen.Next();
      }
    }
}