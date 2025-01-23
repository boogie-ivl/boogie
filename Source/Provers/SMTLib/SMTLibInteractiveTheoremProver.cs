using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Numerics;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibInteractiveTheoremProver : SMTLibProcessTheoremProver
  {
    private bool processNeedsRestart;
    private ScopedNamer commonNamer;
    private ScopedNamer finalNamer;
    private int resourceCount;

    [NotDelayed]
    public SMTLibInteractiveTheoremProver(SMTLibOptions libOptions, SMTLibSolverOptions options, VCExpressionGenerator gen,
      SMTLibProverContext ctx) : base(libOptions, options, gen, ctx) {
      DeclCollector = new TypeDeclCollector(libOptions, new ProverNamer(this));
      SetupProcess();
      if (libOptions.ImmediatelyAcceptCommands) {
        PrepareCommon();
      }
    }

    protected internal override ScopedNamer Namer => finalNamer ?? (commonNamer ??= GetNamer(libOptions, options));

    public override Task GoBackToIdle()
    {
      if (Process == null) {
        processNeedsRestart = true;
        return Task.CompletedTask;
      }
      return Process.PingPong();
    }

    private void PossiblyRestart()
    {
      if (Process != null && processNeedsRestart) {
        processNeedsRestart = false;
        SetupProcess();
        Process.Send(common.ToString());
      }
    }

    private void FlushAndCacheCommons()
    {
      FlushAxioms();
      CachedCommon ??= common.ToString();
    }

    public override int FlushAxiomsToTheoremProver()
    {
      // we feed the axioms when BeginCheck is called.
      return 0;
    }

    private bool hasReset = true;
    public override async Task<SolverOutcome> Check(string descriptiveName, VCExpr vc, ErrorHandler handler, int errorLimit, CancellationToken cancellationToken)
    {
      currentErrorHandler = handler;
      try
      {
        if (options.SeparateLogFiles)
        {
          CloseLogFile(); // shouldn't really happen
        }

        if (options.LogFilename != null && currentLogFile == null)
        {
          currentLogFile = OpenOutputFile(descriptiveName);
          await currentLogFile.WriteAsync(common.ToString());
        }

        if (HadErrors)
        {
          HadErrors = false;
          processNeedsRestart = true;
        }

        PrepareCommon();
        FlushAndCacheCommons();

        OptimizationRequests.Clear();

        PossiblyRestart();

        if (hasReset)
        {
          AxBuilder = (TypeAxiomBuilder) CachedAxBuilder?.Clone();
          finalNamer = ResetNamer(commonNamer);
        }

        SendThisVC("(push 1)");
        DeclCollector.Push();
        string vcString = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";
        FlushAxioms();
        SendVCId(descriptiveName);
        SendVCOptions();
        SendThisVC(vcString);

        SendOptimizationRequests();

        FlushLogFile();

        if (Process != null)
        {
          await Process.PingPong(); // flush any errors
          Process.NewProblem(descriptiveName);
        }

        DeclCollector.Pop();
        if (hasReset)
        {
          common = new StringBuilder(CachedCommon);
          hasReset = false;
        }

        var result = await CheckSat(cancellationToken, errorLimit);
        SendThisVC("(pop 1)");

        return result;
      }
      finally
      {
        currentErrorHandler = null;
      }
    }

    public override async Task Reset(VCExpressionGenerator generator)
    {
      gen = generator;
      SendThisVC("(reset)");
      await RecoverIfProverCrashedAfterReset();
      if (0 < common.Length)
      {
        var c = common.ToString();
        Process.Send(c);
        if (currentLogFile != null)
        {
          currentLogFile.WriteLine(c);
        }
      }

      hasReset = true;
    }

    private async Task RecoverIfProverCrashedAfterReset()
    {
      if (await Process.GetExceptionIfProverDied() is not null)
      {
        // We recover the process but don't issue the `(reset)` command that fails.
        SetupProcess();
      }
    }

    public override void FullReset(VCExpressionGenerator generator)
    {
      gen = generator;
      SendThisVC("(reset)");
      if (options.Solver == SolverKind.Z3 || options.Solver == SolverKind.NoOpWithZ3Options) {
        SendThisVC("(set-option :" + Z3.RlimitOption + " 0)");
      }
      commonNamer = null;
      finalNamer = null;
      hasReset = true;
      common.Clear();
      SetupAxiomBuilder(gen);
      Axioms.Clear();
      TypeDecls.Clear();
      AxiomsAreSetup = false;
      ctx.Reset();
      ctx.KnownDatatypes.Clear();
      ctx.parent = this;
      DeclCollector.Reset();
      NamedAssumes.Clear();
      SendThisVC("; did a full reset");
    }

    [NoDefaultContract]
    public async Task<SolverOutcome> CheckSat(CancellationToken cancellationToken,
      int errorLimit)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = SolverOutcome.Undetermined;

      if (Process == null || HadErrors)
      {
        return result;
      }
      var errorsDiscovered = 0;

      var globalResult = SolverOutcome.Undetermined;

      while (true)
      {
        string[] labels = null;
        var popLater = false;

        try
        {
          errorsDiscovered++;

          result = await CheckSatAndGetResponse(cancellationToken);

          var reporter = currentErrorHandler;
          // TODO(wuestholz): Is the reporter ever null?
          if (usingUnsatCore && result == SolverOutcome.Valid && reporter != null && 0 < NamedAssumes.Count)
          {
            if (usingUnsatCore)
            {
              var resp = await SendVcRequest("(get-unsat-core)").WaitAsync(cancellationToken);
              ReportCoveredElements(resp);
            }
          }

          if (libOptions.RunDiagnosticsOnTimeout && result == SolverOutcome.TimeOut) {
            (result, popLater) = await RunTimeoutDiagnostics(currentErrorHandler, result, cancellationToken);
          }

          if (globalResult == SolverOutcome.Undetermined)
          {
            globalResult = result;
          }

          if (result == SolverOutcome.Invalid)
          {
            Model model = await GetErrorModel(cancellationToken);
            if (libOptions.SIBoolControlVC)
            {
              labels = Array.Empty<string>();
            }
            else
            {
              labels = await CalculatePath(currentErrorHandler.StartingProcId(), cancellationToken);
              if (labels.Length == 0)
              {
                // Without a path to an error, we don't know what to report
                globalResult = SolverOutcome.Undetermined;
                break;
              }
            }

            currentErrorHandler.OnModel(labels, model, result);
          }

          // if the solver is out of resources or has timed out, the global result needs to reflect that.
          if (result == SolverOutcome.OutOfResource || result == SolverOutcome.TimeOut) {
            globalResult = result;
          }

          Debug.Assert(errorsDiscovered > 0);
          // if errorLimit is 0, loop will break only if there are no more 
          // counterexamples to be discovered or the solver is out of resources
          // or has timed out.
          if (labels == null || !labels.Any() || errorsDiscovered == errorLimit)
          {
            break;
          }
        }
        finally
        {
          if (popLater)
          {
            SendThisVC("(pop 1)");
          }
        }

        var source = labels[^2];
        var target = labels[^1];
        // block the assert which was falsified by this counterexample
        SendThisVC($"(assert (not (= (ControlFlow 0 {source}) (- {target}))))");
      }

      FlushLogFile();

      if (libOptions.RestartProverPerVC && Process != null)
      {
        processNeedsRestart = true;
      }

      return globalResult;
    }

    // TODO seems like there's a sort of empty line being returned that we can use to check that the solver is done, but this code doesn't use it.
    private Task<SExpr> SendVcRequest(string s) {
      s = Sanitize(s);

      if (currentLogFile != null)
      {
        currentLogFile.WriteLine(s);
        currentLogFile.Flush();
      }

      return Process.SendRequest(s);
    }

    private T WrapInPushPop<T>(ref bool popLater, Func<T> action)
    {
      if (popLater)
      {
        SendThisVC("(pop 1)");
      }
      SendThisVC("(push 1)");
      var result = action();
      popLater = true;
      return result;
    }

    private async Task<(SolverOutcome, bool)> RunTimeoutDiagnostics(ErrorHandler handler, SolverOutcome result, CancellationToken cancellationToken)
    {
      var popLater = false;
      if (libOptions.TraceDiagnosticsOnTimeout) {
        libOptions.OutputWriter.WriteLine("Starting timeout diagnostics with initial time limit {0}.", options.TimeLimit);
      }

      SendThisVC("; begin timeout diagnostics");

      var start = DateTime.UtcNow;
      var unverified = new SortedSet<int>(ctx.TimeoutDiagnosticIDToAssertion.Keys);
      var timedOut = new SortedSet<int>();
      var frac = 2;
      var queries = 0;
      var timeLimitPerAssertion = 0 < options.TimeLimit
        ? (options.TimeLimit / 100) * libOptions.TimeLimitPerAssertionInPercent
        : 1000;
      while (true) {
        var rem = unverified.Count;
        if (rem == 0) {
          if (0 < timedOut.Count) {
            
            result = await WrapInPushPop(ref popLater, () => CheckSplit(timedOut, options.TimeLimit, timeLimitPerAssertion, ref queries, cancellationToken));
            if (result == SolverOutcome.Valid) {
              timedOut.Clear();
            } else if (result == SolverOutcome.TimeOut) {
              // Give up and report which assertions were not verified.
              var cmds = timedOut.Select(id => ctx.TimeoutDiagnosticIDToAssertion[id]);

              if (cmds.Any()) {
                handler.OnResourceExceeded("timeout after running diagnostics", cmds);
              }
            }
          } else {
            result = SolverOutcome.Valid;
          }

          break;
        }

        // TODO(wuestholz): Try out different ways for splitting up the work (e.g., randomly).
        var cnt = Math.Max(1, rem / frac);
        // It seems like assertions later in the control flow have smaller indexes.
        var split = new SortedSet<int>(unverified.Where((val, idx) => (rem - idx - 1) < cnt));
        Contract.Assert(0 < split.Count);
        
        var splitRes = await WrapInPushPop(ref popLater, () => CheckSplit(split, timeLimitPerAssertion, timeLimitPerAssertion,
          ref queries, cancellationToken));
        if (splitRes == SolverOutcome.Valid) {
          unverified.ExceptWith(split);
          frac = 1;
        } else if (splitRes == SolverOutcome.Invalid) {
          result = splitRes;
          break;
        } else if (splitRes == SolverOutcome.TimeOut) {
          if (2 <= frac && (4 <= (rem / frac))) {
            frac *= 4;
          } else if (2 <= (rem / frac)) {
            frac *= 2;
          } else {
            timedOut.UnionWith(split);
            unverified.ExceptWith(split);
            frac = 1;
          }
        } else {
          break;
        }
      }

      unverified.UnionWith(timedOut);

      var end = DateTime.UtcNow;

      SendThisVC("; end timeout diagnostics");

      if (libOptions.TraceDiagnosticsOnTimeout) {
        libOptions.OutputWriter.WriteLine("Terminated timeout diagnostics after {0:F0} ms and {1} prover queries.",
          end.Subtract(start).TotalMilliseconds, queries);
        libOptions.OutputWriter.WriteLine("Outcome: {0}", result);
        libOptions.OutputWriter.WriteLine("Unverified assertions: {0} (of {1})", unverified.Count,
          ctx.TimeoutDiagnosticIDToAssertion.Keys.Count);

        var filename = "unknown";
        var assertion = ctx.TimeoutDiagnosticIDToAssertion.Values.Select(t => t.Item1)
          .FirstOrDefault(a => a.tok != null && a.tok != Token.NoToken && a.tok.filename != null);
        if (assertion != null) {
          filename = assertion.tok.filename;
        }

        File.AppendAllText("timeouts.csv",
          string.Format(";{0};{1};{2:F0};{3};{4};{5};{6}\n", filename, options.TimeLimit,
            end.Subtract(start).TotalMilliseconds, queries, result, unverified.Count,
            ctx.TimeoutDiagnosticIDToAssertion.Keys.Count));
      }

      return (result, popLater);
    }

    private Task<SolverOutcome> CheckSplit(SortedSet<int> split, uint timeLimit, uint timeLimitPerAssertion,
      ref int queries, CancellationToken cancellationToken)
    {
      var tla = (uint)(timeLimitPerAssertion * split.Count);

      // FIXME: Gross. Timeout should be set in one place! This is also Z3 specific!
      var newTimeout = (0 < tla && tla < timeLimit) ? tla : timeLimit;
      if (newTimeout > 0)
      {
        SendThisVC(string.Format("(set-option :{0} {1})", Z3.TimeoutOption, newTimeout));
      }

      SendThisVC(string.Format("; checking split VC with {0} unverified assertions", split.Count));
      var expr = VCExpressionGenerator.True;
      foreach (var i in ctx.TimeoutDiagnosticIDToAssertion.Keys)
      {
        var lit = VCExprGen.Function(VCExpressionGenerator.TimeoutDiagnosticsOp,
          VCExprGen.Integer(BaseTypes.BigNum.FromInt(i)));
        if (split.Contains(i))
        {
          lit = VCExprGen.Not(lit);
        }

        expr = VCExprGen.AndSimp(expr, lit);
      }

      SendThisVC("(assert " + VCExpr2String(expr, 1) + ")");
      if (options.Solver == SolverKind.Z3)
      {
        SendThisVC("(apply (then (using-params propagate-values :max_rounds 1) simplify) :print false)");
      }

      FlushLogFile();
      queries++;
      return CheckSatAndGetResponse(cancellationToken);
    }

    private async Task<string[]> CalculatePath(int controlFlowConstant, CancellationToken cancellationToken)
    {
      var path = new List<string>();
      string v = "0";
      while (true)
      {
        var response = await Process.SendRequest($"(get-value (({VCExpressionGenerator.ControlFlowName} {controlFlowConstant} {v})))", cancellationToken);
        if (response == null)
        {
          break;
        }

        if (!(response.Name == "" && response.ArgCount == 1))
        {
          break;
        }

        response = response.Arguments[0];
        if (!(response.Name == "" && response.ArgCount == 2))
        {
          break;
        }

        response = response.Arguments[1];
        v = response.Name;
        if (v == "-" && response.ArgCount == 1)
        {
          v = response.Arguments[0].Name;
          path.Add(v);
          break;
        }
        else if (response.ArgCount != 0)
        {
          break;
        }

        path.Add(v);
      }

      return path.ToArray();
    }

    private async Task<Model> GetErrorModel(CancellationToken cancellationToken)
    {
      if (!libOptions.ExpectingModel)
      {
        return null;
      }

      var resp = await SendVcRequest("(get-model)").WaitAsync(cancellationToken);
      return resp != null ? ParseErrorModel(resp) : null;
    }

    private async Task<SolverOutcome> CheckSatAndGetResponse(CancellationToken cancellationToken)
    {
      var result = SolverOutcome.Undetermined;
      var wasUnknown = false;

      var checkSatResponse = await SendVcRequest("(check-sat)").WaitAsync(cancellationToken);
      if (checkSatResponse != null)
      {
        result = ParseOutcome(checkSatResponse, out wasUnknown);
      }

      if (wasUnknown)
      {
        var getInfoResponse = await SendVcRequest("(get-info :reason-unknown)").WaitAsync(cancellationToken);
        if (getInfoResponse != null)
        {
          result = ParseReasonUnknown(getInfoResponse, result);
          if (result == SolverOutcome.OutOfMemory) {
            processNeedsRestart = true;
          }
        }
      }

      if (options.Solver == SolverKind.Z3) {
        resourceCount = ParseRCount(await SendVcRequest($"(get-info :{Z3.RlimitOption})"));
        // Sometimes Z3 doesn't tell us that it ran out of resources
        if (result != SolverOutcome.Valid && resourceCount > options.ResourceLimit && options.ResourceLimit > 0) {
          result = SolverOutcome.OutOfResource;
        }
      }

      return result;
    }

    public override async Task<object> Evaluate(VCExpr expr)
    {
      string vcString = VCExpr2String(expr, 1);
      var resp = await SendVcRequest($"(get-value ({vcString}))");
      if (resp == null)
      {
        throw new VCExprEvaluationException();
      }

      if (!(resp.Name == "" && resp.ArgCount == 1))
      {
        throw new VCExprEvaluationException();
      }

      resp = resp.Arguments[0];
      if (resp.Name == "")
      {
        // evaluating an expression
        if (resp.ArgCount == 2)
        {
          resp = resp.Arguments[1];
        }
        else
        {
          throw new VCExprEvaluationException();
        }
      }
      else
      {
        // evaluating a variable
        if (resp.ArgCount == 1)
        {
          resp = resp.Arguments[0];
        }
        else
        {
          throw new VCExprEvaluationException();
        }
      }

      if (resp.Name == "-" && resp.ArgCount == 1) // negative int
      {
        return Microsoft.BaseTypes.BigNum.FromString("-" + resp.Arguments[0].Name);
      }

      if (resp.Name == "_" && resp.ArgCount == 2 && resp.Arguments[0].Name.StartsWith("bv")) // bitvector
      {
        return new BvConst(Microsoft.BaseTypes.BigNum.FromString(resp.Arguments[0].Name.Substring("bv".Length)),
          int.Parse(resp.Arguments[1].Name));
      }

      if (resp.Name == "fp" && resp.ArgCount == 3)
      {
        Func<SExpr, BigInteger> getBvVal = e => BigInteger.Parse(e.Arguments[0].Name.Substring("bv".Length));
        Func<SExpr, int> getBvSize = e => int.Parse(e.Arguments[1].ToString());
        bool isNeg = getBvVal(resp.Arguments[0]).IsOne;
        var expExpr = resp.Arguments[1];
        var sigExpr = resp.Arguments[2];
        BigInteger exp = getBvVal(expExpr);
        int expSize = getBvSize(expExpr);
        BigInteger sig = getBvVal(sigExpr);
        int sigSize = getBvSize(sigExpr) + 1;
        return new BaseTypes.BigFloat(isNeg, sig, exp, sigSize, expSize);
      }

      if (resp.Name == "_" && resp.ArgCount == 3)
      {
        String specialValue = resp.Arguments[0].ToString();
        int expSize = int.Parse(resp.Arguments[1].ToString());
        int sigSize = int.Parse(resp.Arguments[2].ToString());
        return new BaseTypes.BigFloat(specialValue, sigSize, expSize);
      }

      var ary = ParseArrayFromProverResponse(resp);
      if (ary != null)
      {
        return ary;
      }

      if (resp.ArgCount != 0)
      {
        throw new VCExprEvaluationException();
      }

      if (expr.Type.Equals(Boogie.Type.Bool))
      {
        return bool.Parse(resp.Name);
      }
      else if (expr.Type.Equals(Boogie.Type.Int))
      {
        return Microsoft.BaseTypes.BigNum.FromString(resp.Name);
      }
      else
      {
        return resp.Name;
      }
    }

    public override async Task<List<string>> UnsatCore()
    {
      SendThisVC("(get-unsat-core)");
      var resp = await SendVcRequest("(get-unsat-core)");
      return ParseUnsatCore(resp.ToString());
    }

    protected override void Send(string s, bool isCommon)
    {
      s = Sanitize(s);

      if (isCommon)
      {
        common.Append(s).Append("\r\n");
      }

      if (Process != null)
      {
        Process.Send(s);
      }

      if (currentLogFile != null)
      {
        currentLogFile.WriteLine(s);
        currentLogFile.Flush();
      }
    }

    protected override void PrepareCommon() {
      var currentNamer = finalNamer;
      finalNamer = null;
      base.PrepareCommon();
      finalNamer = currentNamer;
    }

    public override int GetRCount()
    {
      if (options.Solver != SolverKind.Z3) {
        // Only Z3 currently supports retrieving this value. CVC5
        // supports setting a limit, but does not appear to support
        // reporting how much it took to complete a query.
        return 0;
      }

      return resourceCount;
    }

    /// <summary>
    /// Extra state for ApiChecker (used by stratifiedInlining)
    /// </summary>
    static int nameCounter;

    public override async Task<(SolverOutcome, List<int>)> CheckAssumptions(List<VCExpr> assumptions,
      ErrorHandler handler, CancellationToken cancellationToken)
    {
      currentErrorHandler = handler;
      try
      {
        Push();
        // Name the assumptions
        var nameToAssumption = new Dictionary<string, int>();
        int i = 0;
        foreach (var vc in assumptions)
        {
          var name = "a" + nameCounter.ToString();
          nameCounter++;
          nameToAssumption.Add(name, i);

          string vcString = VCExpr2String(vc, 1);
          AssertAxioms();
          SendThisVC(string.Format("(assert (! {0} :named {1}))", vcString, name));
          i++;
        }

        PrepareCommon();
        var outcome = await CheckSat(cancellationToken, libOptions.ErrorLimit);

        if (outcome != SolverOutcome.Valid)
        {
          Pop();
          return (outcome, new List<int>());
        }

        Contract.Assert(usingUnsatCore, "SMTLib prover not setup for computing unsat cores");
        var resp = await SendVcRequest("(get-unsat-core)").WaitAsync(cancellationToken);
        var unsatCore = new List<int>();
        if (resp is not null && resp.Name != "")
        {
          unsatCore.Add(nameToAssumption[resp.Name]);
        }

        if (resp is not null)
        {
          foreach (var s in resp.Arguments)
          {
            unsatCore.Add(nameToAssumption[s.Name]);
          }
        }

        FlushLogFile();
        Pop();
        return (outcome, unsatCore);
      }
      finally
      {
        currentErrorHandler = null;
      }
    }

    public override async Task<(SolverOutcome, List<int>)> CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions,
      ErrorHandler handler, CancellationToken cancellationToken)
    {
      currentErrorHandler = handler;
      try
      {
        // First, convert both hard and soft assumptions to SMTLIB strings
        var hardAssumptionStrings = new List<string>();
        foreach (var a in hardAssumptions)
        {
          hardAssumptionStrings.Add(VCExpr2String(a, 1));
        }

        var currAssumptionStrings = new List<string>();
        foreach (var a in softAssumptions)
        {
          currAssumptionStrings.Add(VCExpr2String(a, 1));
        }

        Push();
        AssertAxioms();
        foreach (var a in hardAssumptionStrings)
        {
          SendThisVC("(assert " + a + ")");
        }

        PrepareCommon();
        var outcome = await CheckSatAndGetResponse(cancellationToken);
        if (outcome != SolverOutcome.Invalid)
        {
          Pop();
          return (outcome, new List<int>());
        }

        var k = 0;
        var relaxVars = new List<string>();
        var unsatisfiedSoftAssumptions = new List<int>();
        while (true)
        {
          Push();
          foreach (var a in currAssumptionStrings)
          {
            SendThisVC("(assert " + a + ")");
          }

          PrepareCommon();
          outcome = await CheckSat(cancellationToken, libOptions.ErrorLimit);
          if (outcome != SolverOutcome.Valid)
          {
            break;
          }

          Pop();
          var relaxVar = "relax_" + k;
          relaxVars.Add(relaxVar);
          SendThisVC("(declare-fun " + relaxVar + " () Int)");
          var nextAssumptionStrings = new List<string>();
          for (var i = 0; i < currAssumptionStrings.Count; i++)
          {
            var constraint = "(= " + relaxVar + " " + i + ")";
            nextAssumptionStrings.Add("(or " + currAssumptionStrings[i] + " " + constraint + ")");
          }

          currAssumptionStrings = nextAssumptionStrings;
          k++;
        }

        if (outcome == SolverOutcome.Invalid)
        {
          foreach (var relaxVar in relaxVars)
          {
            var resp = await SendVcRequest($"(get-value ({relaxVar}))").WaitAsync(cancellationToken);
            if (resp == null)
            {
              break;
            }

            if (!(resp.Name == "" && resp.ArgCount == 1))
            {
              break;
            }

            resp = resp.Arguments[0];
            if (!(resp.Name != "" && resp.ArgCount == 1))
            {
              break;
            }

            resp = resp.Arguments[0];
            if (resp.ArgCount != 0)
            {
              break;
            }

            if (int.TryParse(resp.Name, out var v))
            {
              unsatisfiedSoftAssumptions.Add(v);
            }
            else
            {
              break;
            }
          }

          Pop();
        }

        Pop();
        return (outcome, unsatisfiedSoftAssumptions);
      }
      finally
      {
        currentErrorHandler = null;
      }
    }

    protected void SetupProcess()
    {
      Process?.Close();
      Process = libOptions.CreateSolver(libOptions, options);

      Process.ErrorHandler += HandleProverError;
    }

    public override void Close()
    {
      base.Close();
      Process?.Close();
      Process = null;
      CloseLogFile();
    }
  }
}
