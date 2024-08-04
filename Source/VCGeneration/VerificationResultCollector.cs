using System.Collections.Concurrent;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace VC;

public class VerificationResultCollector : VerifierCallback
{
  private readonly VCGenOptions options;

  public VerificationResultCollector(VCGenOptions options) : base(options.PrintProverWarnings)
  {
    this.options = options;
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullElements(examples));
    Contract.Invariant(Cce.NonNullElements(vcResults));
  }

  public readonly ConcurrentQueue<Counterexample> examples = new();
  public readonly ConcurrentQueue<VerificationRunResult> vcResults = new();

  public override void OnCounterexample(Counterexample ce, string /*?*/ reason)
  {
    //Contract.Requires(ce != null);
    ce.InitializeModelStates();
    examples.Enqueue(ce);
  }

  public override void OnUnreachableCode(ImplementationRun run)
  {
    //Contract.Requires(impl != null);
    run.OutputWriter.WriteLine("found unreachable code:");
    ConditionGeneration.EmitImpl(options, run, false);
    // TODO report error about next to last in seq
  }

  public override void OnVCResult(VerificationRunResult result)
  {
    vcResults.Enqueue(result);
  }
}