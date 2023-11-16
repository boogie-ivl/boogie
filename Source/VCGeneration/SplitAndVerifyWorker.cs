using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reactive.Subjects;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using static VC.ConditionGeneration;

namespace VC
{
  class SplitAndVerifyWorker
  {
    public IObservable<(Split split, VCResult vcResult)> BatchCompletions => batchCompletions;
    private readonly Subject<(Split split, VCResult vcResult)> batchCompletions = new();

    private readonly VCGenOptions options;
    private readonly VerifierCallback callback;
    private readonly ModelViewInfo mvInfo;
    private readonly ImplementationRun run;
      
    private readonly int maxKeepGoingSplits;
    private readonly List<Split> manualSplits;
    private double maxVcCost;
    private readonly bool splitOnEveryAssert;
      
    private bool DoSplitting => manualSplits.Count > 1 || KeepGoing || splitOnEveryAssert;
    private bool TrackingProgress => DoSplitting && (callback.OnProgress != null || options.Trace); 
    private bool KeepGoing => maxKeepGoingSplits > 1;

    private VCGen vcGen;
    private Outcome outcome;
    private double remainingCost;
    private double provenCost;
    private int total;
    private int splitNumber;

    private int totalResourceCount;

    public SplitAndVerifyWorker(VCGenOptions options, VCGen vcGen, ImplementationRun run,
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VerifierCallback callback, ModelViewInfo mvInfo,
      Outcome outcome)
    {
      this.options = options;
      this.callback = callback;
      this.mvInfo = mvInfo;
      this.run = run;
      this.outcome = outcome;
      this.vcGen = vcGen;
      var maxSplits = options.VcsMaxSplits;
      VCGen.CheckIntAttributeOnImpl(run, "vcs_max_splits", ref maxSplits);
      
      maxKeepGoingSplits = options.VcsMaxKeepGoingSplits;
      VCGen.CheckIntAttributeOnImpl(run, "vcs_max_keep_going_splits", ref maxKeepGoingSplits);
      
      maxVcCost = options.VcsMaxCost;
      var tmpMaxVcCost = -1;
      VCGen.CheckIntAttributeOnImpl(run, "vcs_max_cost", ref tmpMaxVcCost);
      if (tmpMaxVcCost >= 0)
      {
        maxVcCost = tmpMaxVcCost;
      }
      
      splitOnEveryAssert = options.VcsSplitOnEveryAssert;
      Implementation.CheckBooleanAttribute("vcs_split_on_every_assert", ref splitOnEveryAssert);

      ResetPredecessors(Implementation.Blocks);
      manualSplits = Split.FocusAndSplit(options, run, gotoCmdOrigins, vcGen, splitOnEveryAssert);
      
      if (manualSplits.Count == 1 && maxSplits > 1) {
        manualSplits = Split.DoSplit(manualSplits[0], maxVcCost, maxSplits);
        maxVcCost = 1.0;
      }
      
      splitNumber = DoSplitting ? 0 : -1;
    }

    public async Task<Outcome> WorkUntilDone(CancellationToken cancellationToken)
    {
      TrackSplitsCost(manualSplits);
      try
      {
        await Task.WhenAll(manualSplits.Select(split => DoWorkForMultipleIterations(split, cancellationToken)));
      }
      finally
      {
        batchCompletions.OnCompleted();
      }

      return outcome;
    }

    public int ResourceCount => totalResourceCount;
    /// <summary>
    /// The cumulative time spent processing SMT queries.  When running with
    /// `vcsCores > 1`, this may also include time spent restarting the prover.
    /// </summary>
    public TimeSpan TotalProverElapsedTime { get; private set; }
    
    private void TrackSplitsCost(List<Split> splits)
    {
      if (!TrackingProgress)
      {
        return;
      }

      foreach (var split in splits) {
        remainingCost += split.Cost;
        total++;
      }
    }

    private async Task DoWorkForMultipleIterations(Split split, CancellationToken cancellationToken)
    {
      var currentSplitNumber = DoSplitting ? Interlocked.Increment(ref splitNumber) - 1 : -1;
      split.SplitIndex = currentSplitNumber;
      if (!options.PortfolioVcIterations)
      {
        await Task.WhenAll(Enumerable.Range(0, options.RandomizeVcIterations).Select(iteration =>
          DoWork(iteration, -1, split, cancellationToken)));
        return;
      }

      var totalIterations = options.RandomizeVcIterations;
      var batchSize = options.PortfolioVcBatchSize;
      var numBatches = totalIterations / batchSize;
      var remainder = totalIterations % batchSize;
      if (remainder > 0)
      {
        numBatches++;
      }

      if (options.Trace)
      {
        var splitText = split.SplitIndex == -1 ? "" : $"split #{split.SplitIndex+1}: ";
        await run.OutputWriter.WriteLineAsync($"      {splitText}Attempting verification in {numBatches} batches of size {batchSize}.");
      }

      bool successfulProofFound = false;
      var allTaskResults = new List<(ProverInterface.Outcome outcome, VCResult result)>();

      for (var batch = 0; batch < numBatches && !successfulProofFound; ++batch)
      {
        var currentBatchSize = (batch == numBatches - 1 && remainder > 0) ? remainder : batchSize;

        var batchCopy = batch;
        var taskResults = await Task.WhenAll(Enumerable.Range(0, currentBatchSize).Select(iteration =>
          DoWork(iteration, batchCopy, split, cancellationToken)));
        taskResults.ForEach(res => allTaskResults.Add(res));

        successfulProofFound = taskResults.Any(pair => pair.outcome == ProverInterface.Outcome.Valid);
        if (successfulProofFound)
        {
          if (options.Trace)
          {
            var remainingBatchesText =
              batch < numBatches - 1 ? $" Not executing remaining {numBatches - batch - 1} batches." : "";
            var splitText = split.SplitIndex == -1 ? "" : $"split #{split.SplitIndex+1}: ";
            await run.OutputWriter.WriteLineAsync($"      {splitText}Batch {batch} verified.{remainingBatchesText}");
          }
        } else if (batch == numBatches - 1) {
          // This is the last batch and it was not successful.
          outcome = taskResults.Select(pair => pair.Item1).Aggregate(outcome, MergeOutcomes);
          if (options.Trace)
          {
            var splitText = split.SplitIndex == -1 ? "" : $"split #{split.SplitIndex+1}: ";
            await run.OutputWriter.WriteLineAsync($"      {splitText}All batches failed to verify.");
          }
        } else {
          // This is not the last batch and it was not successful.
          if (options.Trace)
          {
            var splitText = split.SplitIndex == -1 ? "" : $"split #{split.SplitIndex+1}: ";
            await run.OutputWriter.WriteLineAsync($"      {splitText}batch {batch} failed to verify. moving on to batch {batch + 1}....");
          }
        }
      }
      if (outcome == Outcome.TimedOut || outcome == Outcome.OutOfMemory || outcome == Outcome.OutOfResource) {
        ReportSplitErrorResult(split);
      }
      if (outcome == Outcome.Correct)
      {
        await CheckAndReportBrittleness(allTaskResults, split, 20, 30, 5, 1000000);
      }
    }

    private async Task<(ProverInterface.Outcome outcome, VCResult result)>
      DoWork(int iteration, int batch, Split split, CancellationToken cancellationToken)
    {
      var checker = await split.parent.CheckerPool.FindCheckerFor(split.parent, split, cancellationToken);
      try {
        cancellationToken.ThrowIfCancellationRequested();
        await StartCheck(iteration, batch, split, checker, cancellationToken);
        await checker.ProverTask;
        var (newOutcome, result, newResourceCount) = await split.ReadOutcome(iteration, batch, checker, callback);
        var cex = IsProverFailed(newOutcome) ? split.ToCounterexample(checker.TheoremProver.Context) : null;
        TotalProverElapsedTime += checker.ProverRunTime;
        await checker.GoBackToIdle();
        await ProcessResult(split, newOutcome, result, newResourceCount, cex, cancellationToken);
        return (newOutcome, result);
      }
      catch {
        await checker.GoBackToIdle();
        throw;
      }
    }

    private async Task StartCheck(int iteration, int batch, Split split, Checker checker, CancellationToken cancellationToken)
    {
      if (options.Trace && DoSplitting) {
        var splitNum = split.SplitIndex + 1;
        var iterationIdxStr = options.RandomizeVcIterations > 1 ? batch >= 0 ? $" (batch {batch} iteration {iteration})" : $" (iteration {iteration})" : "";
        var splitIdxStr = $"{splitNum}{iterationIdxStr}";
        run.OutputWriter.WriteLine("    checking split {1}/{2}, {3:0.00}%, {0} ...",
          split.Stats, splitIdxStr, total, 100 * provenCost / (provenCost + remainingCost));
      }

      callback.OnProgress?.Invoke("VCprove", split.SplitIndex, total,
        provenCost / (remainingCost + provenCost));

      var timeout = KeepGoing && split.LastChance ? options.VcsFinalAssertTimeout :
        KeepGoing ? options.VcsKeepGoingTimeout :
        run.Implementation.GetTimeLimit(options);
      await split.BeginCheck(run.OutputWriter, checker, callback, mvInfo, timeout, Implementation.GetResourceLimit(options), cancellationToken);
    }

    private Implementation Implementation => run.Implementation;

    private async Task ProcessResult(Split split, ProverInterface.Outcome checkerOutcome, 
      VCResult result, int checkerResourceCount, Counterexample checkerCex, CancellationToken cancellationToken)
    {
      if (TrackingProgress) {
        lock (this) {
          remainingCost -= split.Cost;
        }
      }

      lock (this) {
        if (!options.PortfolioVcIterations) {
          outcome = MergeOutcomes(outcome, checkerOutcome);
        }
        totalResourceCount += checkerResourceCount;
      }
      var proverFailed = IsProverFailed(checkerOutcome);

      if (TrackingProgress) {
        lock (this) {
          if (proverFailed) {
            // even if the prover fails, we have learned something, i.e., it is
            // annoying to watch Boogie say Timeout, 0.00% a couple of times
            provenCost += split.Cost / 100;
          } else {
            provenCost += split.Cost;
          }
        }
      }

      callback.OnProgress?.Invoke("VCprove", splitNumber < 0 ? 0 : splitNumber, total, provenCost / (remainingCost + provenCost));

      if (proverFailed) {
        await HandleProverFailure(split, checkerCex, callback, result, cancellationToken);
      }
      batchCompletions.OnNext((split, result));
    }

    private static bool IsProverFailed(ProverInterface.Outcome outcome)
    {
      switch (outcome)
      {
        case ProverInterface.Outcome.Valid:
        case ProverInterface.Outcome.Invalid:
        case ProverInterface.Outcome.Undetermined:
          return false;
        case ProverInterface.Outcome.OutOfMemory:
        case ProverInterface.Outcome.TimeOut:
        case ProverInterface.Outcome.OutOfResource:
          return true;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private static Outcome MergeOutcomes(Outcome currentOutcome, ProverInterface.Outcome newOutcome)
    {
      switch (newOutcome)
      {
        case ProverInterface.Outcome.Valid:
          return currentOutcome;
        case ProverInterface.Outcome.Invalid:
          return Outcome.Errors;
        case ProverInterface.Outcome.OutOfMemory:
          if (currentOutcome != Outcome.Errors && currentOutcome != Outcome.Inconclusive)
          {
            return Outcome.OutOfMemory;
          }

          return currentOutcome;
        case ProverInterface.Outcome.TimeOut:
          if (currentOutcome != Outcome.Errors && currentOutcome != Outcome.Inconclusive)
          {
            return Outcome.TimedOut;
          }

          return currentOutcome;
        case ProverInterface.Outcome.OutOfResource:
          if (currentOutcome != Outcome.Errors && currentOutcome != Outcome.Inconclusive)
          {
            return Outcome.OutOfResource;
          }

          return currentOutcome;
        case ProverInterface.Outcome.Undetermined:
          if (currentOutcome != Outcome.Errors)
          {
            return Outcome.Inconclusive;
          }
          return currentOutcome;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private async Task HandleProverFailure(Split split, Counterexample cex, VerifierCallback callback, VCResult vcResult, CancellationToken cancellationToken)
    {
      if (split.LastChance && !options.PortfolioVcIterations) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnCounterexample(cex, msg);
        split.Counterexamples.Add(cex);
        // Update one last time the result with the dummy counter-example to indicate the position of the timeout
        var result = vcResult with {
          counterExamples = split.Counterexamples
        };
        batchCompletions.OnNext((split, result));
        outcome = Outcome.Errors;
        return;
      }

      if (maxKeepGoingSplits > 1) {
        var newSplits = Split.DoSplit(split, maxVcCost, maxKeepGoingSplits);
        if (options.Trace) {
          await run.OutputWriter.WriteLineAsync($"split {split.SplitIndex+1} was split into {newSplits.Count} parts");
        }
        Contract.Assert(newSplits != null);
        maxVcCost = 1.0; // for future
        TrackSplitsCost(newSplits);
        
        if (outcome != Outcome.Errors) {
          outcome = Outcome.Correct;
        }
        await Task.WhenAll(newSplits.Select(newSplit => DoWorkForMultipleIterations(newSplit, cancellationToken)));
        return;
      }

      if (options.PortfolioVcIterations) {
        // Errors are handled later when using PortfolioVcIterations.
        return;
      }
      ReportSplitErrorResult(split);
    }

    private void ReportSplitErrorResult(Split split)
    {
      Contract.Assert(outcome != Outcome.Correct);
      if (outcome == Outcome.TimedOut) {
        string msg = "some timeout";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnTimeout(msg);
      } else if (outcome == Outcome.OutOfMemory) {
        string msg = "out of memory";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }

        callback.OnOutOfMemory(msg);
      } else if (outcome == Outcome.OutOfResource) {
        string msg = "out of resource";
        if (split.reporter is { resourceExceededMessage: { } }) {
          msg = split.reporter.resourceExceededMessage;
        }
        callback.OnOutOfResource(msg);
      }
    }

    private async Task CheckAndReportBrittleness(List<(ProverInterface.Outcome outcome, VCResult result)> taskResults,
      Split split, int runTimeCvvhreshold, int resourceCountCvThreshold, int runTimeMeanThreshold, int resourceCountMeanThreshold)
    {
      var numVerified = taskResults.Count(pair => pair.outcome == ProverInterface.Outcome.Valid);
      var numTotalGoals = taskResults.Count;
      var numFailed = numTotalGoals - numVerified;
      var successRatio = (double) numVerified / numTotalGoals;

      // Analyze variances in runTime and resourceCount
      double runTimeSum = 0;
      double resourceCountSum = 0;
      var taskCount = taskResults.Count;

      foreach (var (_, result) in taskResults)
      {
        runTimeSum += result.runTime.TotalSeconds;
        resourceCountSum += result.resourceCount;
      }

      var runTimeMean = runTimeSum / taskCount;
      var resourceCountMean = resourceCountSum / taskCount;

      double runTimeVarianceSum = 0;
      double resourceCountVarianceSum = 0;

      foreach (var (_, result) in taskResults)
      {
        runTimeVarianceSum += Math.Pow(result.runTime.TotalSeconds - runTimeMean, 2);
        resourceCountVarianceSum += Math.Pow(result.resourceCount - resourceCountMean, 2);
      }

      var runTimeStdDev = Math.Sqrt(runTimeVarianceSum / (taskCount - 1));
      var resourceCountStdDev = Math.Sqrt(resourceCountVarianceSum / (taskCount - 1));

      var runTimeCv = (runTimeMean == 0) ? 0 : (runTimeStdDev / runTimeMean) * 100;
      var resourceCountCv = (resourceCountMean == 0) ? 0 : (resourceCountStdDev / resourceCountMean) * 100;

      // Output results
      var splitText = split.SplitIndex == -1 ? "" : $"split #{split.SplitIndex+1}: ";
      var sb = new StringBuilder();

      if (numFailed > 0)
      {
        sb.AppendLine($"    {splitText}Warning: goal is brittle! Ratio of verified / total goals: {numVerified}/{numTotalGoals} ({successRatio:F2})");
      }
      if (runTimeMean > runTimeMeanThreshold && runTimeCv > runTimeCvvhreshold)
      {
        var runTimesList = string.Join(", ", taskResults.Select(t => t.result.runTime.TotalSeconds.ToString("F2")));
        sb.AppendLine($"    Warning: {splitText}Exceeded coefficient of variation for runtimes. Coefficient of Variation: {runTimeCv:F2}%");
        sb.AppendLine($"    Runtimes (seconds): {runTimesList}");
      }
      if (resourceCountMean > resourceCountMeanThreshold && resourceCountCv > resourceCountCvThreshold)
      {
        var resourceCountsList = string.Join(", ", taskResults.Select(t => t.result.resourceCount));
        sb.AppendLine($"    Warning: {splitText}Exceeded coefficient of variation for resource counts. Coefficient of Variation: {resourceCountCv:F2}%");
        sb.AppendLine($"    Resource Counts: {resourceCountsList}");
      }
      await run.OutputWriter.WriteAsync(sb.ToString());
    }
  }
}
