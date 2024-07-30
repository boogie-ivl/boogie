using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using NUnit.Framework;
using VC;


namespace ExecutionEngineTests;

public class FakeDescription : ProofObligationDescription
{
  public override string SuccessDescription => "fake success";
  public override string FailureDescription => "fake failure";
  public override string ShortDescription => "fake";
}

[TestFixture]
public class ExecutionEngineTest {

  [Test]
  public async Task DisposeCleansUpThreads()
  {
    var options = new CommandLineOptions(TextWriter.Null, new ConsolePrinter());
    options.VcsCores = 10;
    int beforeCreation = Process.GetCurrentProcess().Threads.Count;
    var engine = new ExecutionEngine(options, new VerificationResultCache(), 
      CustomStackSizePoolTaskScheduler.Create(ExecutionEngine.StackSize, options.VcsCores), true);
    engine.Dispose();
    for (int i = 0; i < 50; i++)
    {
      await Task.Delay(10);
      int afterDispose = Process.GetCurrentProcess().Threads.Count;
      if (afterDispose + 2 <= beforeCreation + options.VcsCores)
      {
        // It's difficult to access the current managed threads and see if any of the ones we create with the ExecutionEngine are still there,
        // More information on the difficulty: https://stackoverflow.com/questions/10315862/get-list-of-threads
        // So we make this test less precise and only check that the number of OS threads has gone down by at least 2.
        // We're expecting 10 threads to be removed, so even if some other code creates a few more threads we can still expect a drop of 2.
        return;
      }
    }
    Assert.Fail("Thread count didn't drop back down after waiting 500ms.");
  }

  [Test]
  public void ResolutionErrorOnGetVerificationTasks()
  {
    var programString = @"
procedure Procedure(y: int)
  ensures x == true;
{
}
".Trim();
    Parser.Parse(programString, "fakeFilename10", out var program);
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    Assert.Throws<ArgumentException>(() =>
    {
      var tasks = engine.GetVerificationTasks(program);
    });
  }
  
  [Test]
  public void TypeErrorOnGetVerificationTasks()
  {
    var programString = @"
procedure Procedure(y: int)
  ensures y == true;
{
}
".Trim();
    Parser.Parse(programString, "fakeFilename10", out var program);
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    Assert.Throws<ArgumentException>(() =>
    {
      var tasks = engine.GetVerificationTasks(program);
    });
  }

  [Test]
  public async Task SplitOnEveryAssertion() {
    var programString = @"
procedure Procedure(y: int)
  ensures y == 3;
{
  assert y > 2;
  assert y > 1;
  assert y < 4;
}
".Trim();
    Parser.Parse(programString, "fakeFilename10", out var program);
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsSplitOnEveryAssert = true;
    options.PrintErrorModel = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    var tasks = engine.GetVerificationTasks(program);
    
    // The first split is empty. Maybe it can be optimized away
    Assert.AreEqual(5, tasks.Count);

    var outcomes = new List<SolverOutcome> { SolverOutcome.Valid, SolverOutcome.Invalid, SolverOutcome.Valid, SolverOutcome.Invalid, SolverOutcome.Valid };
    for (var index = 0; index < outcomes.Count; index++)
    {
      var result0 = await tasks[index].TryRun()!.ToTask();
      var verificationResult0 = ((Completed)result0).Result;
      Assert.AreEqual(outcomes[index], verificationResult0.Outcome);
    }
  }
  
  [Test]
  public async Task GetImplementationTasksTest() {
    var programString = @"
procedure First(y: int)
{
  assert 2 == 1;
}

procedure Second(y: int)
{
  assert 2 == 2;
}
".Trim();
    Parser.Parse(programString, "fakeFilename10", out var program);
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.PrintErrorModel = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    var tasks = engine.GetVerificationTasks(program);
    Assert.AreEqual(2, tasks.Count);
    Assert.NotNull(tasks[0].Split.Implementation);
    var result1 = await tasks[0].TryRun()!.ToTask();
    var verificationResult1 = ((Completed)result1).Result;
    Assert.AreEqual(SolverOutcome.Invalid, verificationResult1.Outcome);
    Assert.AreEqual(true, verificationResult1.CounterExamples[0].Model.ModelHasStatesAlready);

    Assert.IsTrue(tasks[1].IsIdle);
    var runningStates = tasks[1].TryRun()!;
    Assert.IsFalse(tasks[1].IsIdle);
    var result2 = await runningStates.ToTask();
    Assert.IsTrue(tasks[1].IsIdle);
    var verificationResult2 = ((Completed)result2).Result;
    Assert.AreEqual(SolverOutcome.Valid, verificationResult2.Outcome);
  }

  [Test]
  public async Task VerifyProceduresConcurrently()
  {

    var programString = @"procedure Bad(y: int)
{
  assert 2 == 1;
}

procedure Bad2(y: int)
{
  assert 2 == 3;
}
";
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsCores = 4;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var expected = @"fakeFilename1(3,3): Error: this assertion could not be proved
Execution trace:
    fakeFilename1(3,3): anon0
fakeFilename1(8,3): Error: this assertion could not be proved
Execution trace:
    fakeFilename1(8,3): anon0

Boogie program verifier finished with 0 verified, 2 errors
".ReplaceLineEndings();

    for (int i = 0; i < 300; i++) {
      var writer = new StringWriter();
      Parser.Parse(programString, "fakeFilename1", out var program);
      await engine.ProcessProgram(writer, program, "fakeFilename");
      var result = writer.ToString();
      Assert.AreEqual(expected, result, $"iteration {i}, result {result}");
    }
  }

  [Test]
  public async Task ConcurrentInferAndVerifyCalls() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsCores = 4;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var writer = new StringWriter();
    var concurrentWriterManager = new ConcurrentToSequentialWriteManager(writer);

    var programString = @"procedure Bad(y: int)
{
  assert 2 == 1;
}

procedure Good(y: int)
{
  assert 2 == 2;
}
";
    Parser.Parse(programString, "fakeFilename1", out var program1);
    Parser.Parse(programString, "fakeFilename2", out var program2);
    var task1Writer = concurrentWriterManager.AppendWriter();
    var task1 = engine.ProcessProgram(task1Writer, program1, "fakeFilename1");
    var task2Writer = concurrentWriterManager.AppendWriter();
    var task2 = engine.ProcessProgram(task2Writer, program2, "fakeFilename2");
    await Task.WhenAll(task1, task2);

    await task1Writer.DisposeAsync();
    await task2Writer.DisposeAsync();
    var output = writer.ToString();
    var expected = @"fakeFilename1(3,3): Error: this assertion could not be proved
Execution trace:
    fakeFilename1(3,3): anon0

Boogie program verifier finished with 1 verified, 1 error
fakeFilename2(3,3): Error: this assertion could not be proved
Execution trace:
    fakeFilename2(3,3): anon0

Boogie program verifier finished with 1 verified, 1 error
".ReplaceLineEndings();
    Assert.AreEqual(expected, output);
  }

  [Test]
  public async Task LoopInvariantDescriptions()
  {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var writer = new StringWriter();

    var programString = @"procedure Test()
{
  var i: int;

  entry:
    i := 0;
    goto block850;

  block850:
    assert i == 0;
    havoc i;
    goto block850;

}
";

    Parser.Parse(programString, "fakeFilename", out var program1);
    foreach (var block in program1.Implementations.First().Blocks) {
      foreach (var cmd in block.cmds) {
        if (cmd is AssertCmd assertCmd) {
          assertCmd.Description = new FakeDescription();
        }
      }
    }

    await engine.ProcessProgram(writer, program1, "fakeFilename");
    await writer.DisposeAsync();
    var output = writer.ToString();
    var expected = @"fakeFilename(10,5): Error: this invariant could not be proved to be maintained by the loop
fakeFilename(10,5): Related message: fake failure
Execution trace:
    fakeFilename(5,3): entry
    fakeFilename(9,3): block850

Boogie program verifier finished with 0 verified, 1 error
".ReplaceLineEndings();

    Assert.AreEqual(expected, output);
  }

  [Test]
  public async Task RunCancelRunCancel() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsCores = 1;
    options.CreateSolver = (_, _) => new UnsatSolver(new SemaphoreSlim(0));
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var source = @"
procedure Foo(x: int) {
  assert true;
}".TrimStart();
    var result = Parser.Parse(source, "fakeFilename1", out var program);
    Assert.AreEqual(0, result);
    var tasks = engine.GetVerificationTasks(program)[0];
    var statusList1 = new List<IVerificationStatus>();
    var firstStatuses = tasks.TryRun()!;
    await firstStatuses.Where(s => s is Running).FirstAsync().ToTask();
    firstStatuses.Subscribe(statusList1.Add);
    tasks.Cancel();

    var secondStatuses = tasks.TryRun()!;
    tasks.Cancel();
    var statusList2 = new List<IVerificationStatus>();
    secondStatuses.Subscribe(statusList2.Add);
    await secondStatuses.DefaultIfEmpty().ToTask();
    var expected1 = new List<IVerificationStatus>() {
      new Running(), new Stale()
    };
    Assert.AreEqual(expected1, statusList1);
    var expected2 = new List<IVerificationStatus>() {
      new Stale()
    };
    Assert.AreEqual(expected2, statusList2.TakeLast(1));
  }

  [Test]
  public async Task SingleTaskRunRunCancelRunRun() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    var returnCheckSat = new SemaphoreSlim(0);
    options.VcsCores = 1;
    options.CreateSolver = (_, _) => new UnsatSolver(returnCheckSat);
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var source = @"
procedure Foo(x: int) {
  assert true;
}".TrimStart();
    var result = Parser.Parse(source, "fakeFilename1", out var program);
    Assert.AreEqual(0, result);
    var task = engine.GetVerificationTasks(program)[0];
    var statusList1 = new List<IVerificationStatus>();
    var firstStatuses = task.TryRun()!;
    var runDuringRun1 = task.TryRun();
    Assert.AreEqual(null, runDuringRun1);
    firstStatuses.Subscribe(statusList1.Add);
    task.Cancel();

    var secondStatuses = task.TryRun()!;
    var runDuringRun2 = task.TryRun();
    Assert.AreEqual(null, runDuringRun2);
    var statusList2 = new List<IVerificationStatus>();
    secondStatuses.Subscribe(statusList2.Add);
    while (statusList1.Last() is not Stale)
    {
      await Task.Delay(10);
    }
    returnCheckSat.Release(2);
    var finalResult = await secondStatuses.ToTask();
    Assert.IsTrue(finalResult is Completed);
    var expected1 = new List<IVerificationStatus>() {
      new Running(), new Stale()
    };
    Assert.AreEqual(expected1, statusList1);
    var expected2 = new List<IVerificationStatus>() {
      new Running(), finalResult
    };
    Assert.AreEqual(expected2, statusList2.Where(s => s is not Queued));
  }

  [Test]
  public async Task FromSeedResetsState() {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsCores = 1;
    options.VerifySnapshots = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var source = @"
procedure {:priority 3} {:checksum ""stable""} Bad(y: int)
{
  assert 2 == 1;
}".TrimStart();
    Parser.Parse(source, "fakeFilename1", out var program);
    Assert.AreEqual("Bad", program.Implementations.ElementAt(0).Name);
    var tasks = engine.GetVerificationTasks(program);
    var task = tasks[0];
    await task.TryRun()!.ToTask();
    var secondResult = task.FromSeed(100).TryRun()!;
    var statusList = new List<IVerificationStatus>();
    secondResult.Subscribe(t => statusList.Add(t));
    await secondResult.ToTask();
    Assert.True(statusList.OfType<Running>().Any());
  }
  
  [Test]
  public async Task StatusTest() {
    
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.VcsCores = 1;
    options.VerifySnapshots = 1;
    var engine = ExecutionEngine.CreateWithoutSharedCache(options);

    var programString = @"procedure {:priority 3} {:checksum ""stable""} Bad(y: int)
{
  assert 2 == 1;
}

procedure {:priority 2} {:checksum ""stable""} Good(y: int)
{
  assert 2 == 2;
}
";
    Parser.Parse(programString, "fakeFilename1", out var program);
    Assert.AreEqual("Bad", program.Implementations.ElementAt(0).Name);
    var tasks = engine.GetVerificationTasks(program);
    var statusList = new List<(string, IVerificationStatus)>();

    var first = tasks[0];
    var second = tasks[1];
    var firstName = first.Split.Implementation.Name;
    var secondName = second.Split.Implementation.Name;
    Assert.AreEqual("Bad", firstName);
    Assert.AreEqual("Good", secondName);

    Assert.True(first.CacheStatus is Stale);
    Assert.True(second.CacheStatus is Stale);

    var firstStatuses = first.TryRun()!;
    firstStatuses.Subscribe(t => statusList.Add(new (firstName, t)));
    var secondStatuses = second.TryRun()!;
    secondStatuses.Subscribe(t => statusList.Add((secondName, t)));
    await firstStatuses.Concat(secondStatuses).ToTask();

    Assert.AreEqual((firstName, new Running()), statusList[0]);
    Assert.AreEqual((secondName, new Queued()), statusList[1]);
    Assert.AreEqual(firstName, statusList[2].Item1);
    Assert.AreEqual(firstName, statusList[2].Item1);
    Assert.IsTrue(statusList[2].Item2 is Completed);
    Assert.AreEqual((secondName, new Running()), statusList[3]);
    Assert.AreEqual(secondName, statusList[4].Item1);
    Assert.IsTrue(statusList[4].Item2 is Completed);
  
    Assert.True(tasks[0].CacheStatus is Completed);
    Assert.AreEqual(SolverOutcome.Invalid, ((Completed)tasks[0].CacheStatus).Result.Outcome);

    Assert.True(tasks[1].CacheStatus is Completed);
    Assert.AreEqual(SolverOutcome.Valid, ((Completed)tasks[1].CacheStatus).Result.Outcome);

    // Caching is currently not working
    // var tasks2 = engine.GetVerificationTasks(program);
    // Assert.True(tasks2[0].CacheStatus is Completed);
    // Assert.AreEqual(SolverOutcome.Invalid, ((Completed)tasks2[0].CacheStatus).Result.Outcome);
    //
    // Assert.True(tasks2[1].CacheStatus is Completed);
    // Assert.AreEqual(SolverOutcome.Valid, ((Completed)tasks2[1].CacheStatus).Result.Outcome);
    
    var batchResult = (Completed) statusList[2].Item2;
    
    var assertion = batchResult.Result.Asserts[0];
    batchResult.Result.ComputePerAssertOutcomes(out var perAssertOutcome, out var perAssertCounterExamples);
    Assert.Contains(assertion, perAssertOutcome.Keys);
    Assert.Contains(assertion, perAssertCounterExamples.Keys);
    var outcomeAssertion = perAssertOutcome[assertion];
    var counterExampleAssertion = perAssertCounterExamples[assertion];
    Assert.AreEqual(SolverOutcome.Invalid, outcomeAssertion);
    Assert.AreEqual(true, counterExampleAssertion is AssertCounterexample);
    var assertCounterexample = (AssertCounterexample)counterExampleAssertion;
    Assert.AreEqual(assertCounterexample.FailingAssert, assertion);
  }
  

  [Test]
  public async Task SolverCrash()
  {
    var printer = new NullPrinter();
    var options = CommandLineOptions.FromArguments(TextWriter.Null, printer);
    options.CreateSolver = (_, _) => new OverflowSolver();
    var executionEngine = ExecutionEngine.CreateWithoutSharedCache(options);

    var terminatingProgram = GetProgram(executionEngine, fast);

    // We limit the number of checkers to 1.
    options.VcsCores = 1;

    var outcome1 = await executionEngine.GetVerificationTasks(terminatingProgram)[0].TryRun()!.ToTask();
    Assert.IsTrue(outcome1 is Completed completed && completed.Result.Outcome == SolverOutcome.Undetermined);
    options.CreateSolver = (_ ,_ ) => new UnsatSolver();
    var outcome2 = await executionEngine.GetVerificationTasks(terminatingProgram)[0].TryRun()!.ToTask();
    Assert.IsTrue(outcome2 is Completed completed2 && completed2.Result.Outcome == SolverOutcome.Valid);
  }

  [Test]
  public async Task ConsistentErrorTraceAfterMultipleVerificationAttempts() {
    const string augmentedTraceNonce = "12345"; // will appear in execution trace
    const string programString = @"
procedure Test() {
  assume {:print " + augmentedTraceNonce + @"} true;
  assert false;
}";
    Parser.Parse(programString, "fakeFilename", out var program);
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.EnhancedErrorMessages = 1;
    var output = await ProcessProgramAndGetOutput(program, options);
    Assert.True(output.Contains(augmentedTraceNonce));
    // Now repeat verification again and make sure the augmented trace still shows up
    output = await ProcessProgramAndGetOutput(program, options);
    Assert.True(output.Contains(augmentedTraceNonce));
  }

  private static async Task<string> ProcessProgramAndGetOutput(Program program, CommandLineOptions options) {
    var writer = new StringWriter();
    using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
      await engine.ProcessProgram(writer, program, "fakeFilename");
    }
    await writer.DisposeAsync();
    return writer.ToString();
  }

  private readonly string fast = @"
procedure easy() ensures 1 + 1 == 0; {
}
";

  public Program GetProgram(ExecutionEngine engine, string code) {
    var bplFileName = "1";
    int errorCount = Parser.Parse(code, bplFileName, out Program program,
      engine.Options.UseBaseNameForFileName);
    Assert.AreEqual(0, errorCount);

    engine.ResolveAndTypecheck(program, bplFileName, out _);
    engine.EliminateDeadVariables(program);
    engine.CollectModSets(program);
    engine.CoalesceBlocks(program);
    engine.Inline(program);
    return program;
  }
}