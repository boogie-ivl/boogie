using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;

namespace VC
{
  public record VerificationRunResult
  (
    int VcNum,
    int Iteration,
    DateTime StartTime,
    SolverOutcome Outcome,
    TimeSpan RunTime,
    int MaxCounterExamples,
    List<Counterexample> CounterExamples,
    List<AssertCmd> Asserts,
    IEnumerable<TrackedNodeComponent> CoveredElements,
    int ResourceCount,
    SolverKind? SolverUsed,
    IReadOnlyList<Declaration> DeclarationsAfterPruning
  ) {
    public void ComputePerAssertOutcomes(out Dictionary<AssertCmd, SolverOutcome> perAssertOutcome,
      out Dictionary<AssertCmd, Counterexample> perAssertCounterExamples) {
      perAssertOutcome = new();
      perAssertCounterExamples = new();
      if (Outcome == SolverOutcome.Valid) {
        perAssertOutcome = Asserts.ToDictionary(cmd => cmd, _ => SolverOutcome.Valid);
      } else {
        foreach (var counterExample in CounterExamples)
        {
          var underlyingAssert = counterExample.FailingAssert;

          // We ensure that the underlyingAssert is among the original asserts
          if (!Asserts.Contains(underlyingAssert)) {
            continue;
          }

          perAssertOutcome.TryAdd(underlyingAssert, SolverOutcome.Invalid);
          perAssertCounterExamples.TryAdd(underlyingAssert, counterExample);
        }

        var remainingOutcome =
          Outcome == SolverOutcome.Invalid && CounterExamples.Count < MaxCounterExamples
            // We could not extract more counterexamples, remaining assertions are thus valid 
            ? SolverOutcome.Valid
            : Outcome == SolverOutcome.Invalid
              // We reached the maximum number of counterexamples, we can't infer anything for the remaining assertions
              ? SolverOutcome.Undetermined
              // TimeOut, OutOfMemory, OutOfResource, Undetermined for a single split also applies to assertions
              : Outcome;

        foreach (var assert in Asserts) {
          perAssertOutcome.TryAdd(assert, remainingOutcome);
        }
      }
    }
  }
}
