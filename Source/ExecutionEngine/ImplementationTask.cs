using System;
using System.IO;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

public interface IVerificationStatus {}

/// <summary>
/// Results are available
/// </summary>
public record Completed(VerificationResult Result) : IVerificationStatus;

/// <summary>
/// Scheduled to be run but waiting for resources
/// </summary>
public record Queued : IVerificationStatus;

/// <summary>
/// Not scheduled to be run
/// </summary>
public record Stale : IVerificationStatus;

/// <summary>
/// Currently being run
/// </summary>
public record Running : IVerificationStatus;

public interface IImplementationTask {
  IVerificationStatus CacheStatus { get; }

  ProcessedProgram ProcessedProgram { get; }
  Implementation Implementation { get; }

  IObservable<IVerificationStatus> Run();
  void Cancel();

  bool IsRunning { get; }
}

public class ImplementationTask : IImplementationTask {
  private readonly ExecutionEngine engine;

  public IVerificationStatus CacheStatus { get; private set; }

  public ProcessedProgram ProcessedProgram { get; }

  public Implementation Implementation { get; }
  
  public ImplementationTask(ExecutionEngine engine, ProcessedProgram processedProgram, Implementation implementation) {
    this.engine = engine;
    ProcessedProgram = processedProgram;
    Implementation = implementation;
    
    var cachedVerificationResult = engine.GetCachedVerificationResult(Implementation, TextWriter.Null);
    if (cachedVerificationResult != null) {
      CacheStatus = new Completed(cachedVerificationResult);
    } else {
      CacheStatus = new Stale();
    }
  }

  private CancellationTokenSource cancellationSource;

  public void Cancel() {
    if (cancellationSource == null) {
      throw new InvalidOperationException("There is no ongoing run to cancel.");
    }

    cancellationSource.Cancel();
    cancellationSource = null;
  }

  public bool IsRunning => cancellationSource != null;

  public IObservable<IVerificationStatus> Run()
  {
    if (CacheStatus is not Stale) {
      throw new InvalidOperationException("Can not start task that's already completed");
    }

    if (cancellationSource != null) {
      throw new InvalidOperationException("There already an ongoing run.");
    }
    cancellationSource = new();
    var cancellationToken = cancellationSource.Token;

    var observableStatus = new ReplaySubject<IVerificationStatus>();
    cancellationToken.Register(() => {
      observableStatus.OnNext(new Stale());
      observableStatus.OnCompleted();
    });
    var task = RunInternal(cancellationToken, observableStatus.OnNext);
    task.ContinueWith(r =>
    {
      if (r.Exception != null) {
        observableStatus.OnError(r.Exception);
      } else {
        observableStatus.OnCompleted();
      }
    }, TaskScheduler.Current);
    return observableStatus;
  }

  private async Task<VerificationResult> RunInternal(CancellationToken cancellationToken, Action<IVerificationStatus> notifyStatusChange) {

    var enqueueTask = engine.EnqueueVerifyImplementation(ProcessedProgram, new PipelineStatistics(),
      null, null, Implementation, cancellationToken, TextWriter.Null);

    var afterEnqueueStatus = enqueueTask.IsCompleted ? (IVerificationStatus)new Running() : new Queued();
    notifyStatusChange(afterEnqueueStatus);

    var verifyTask = await enqueueTask;
    if (afterEnqueueStatus is not Running) {
      notifyStatusChange(new Running());
    }

    var result = await verifyTask;
    CacheStatus = new Completed(result);
    cancellationSource = null;
    notifyStatusChange(CacheStatus);
    return result;
  }
}