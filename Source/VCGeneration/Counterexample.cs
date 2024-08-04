using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;
using VC;
using VCGeneration;

namespace Microsoft.Boogie
{
  public class CalleeCounterexampleInfo
  {
    public Counterexample counterexample;

    public List<object> /*!>!*/
      args;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(args));
    }

    public CalleeCounterexampleInfo(Counterexample cex, List<object /*!>!*/> x)
    {
      Contract.Requires(Cce.NonNullElements(x));
      counterexample = cex;
      args = x;
    }
  }

  public class TraceLocation : IEquatable<TraceLocation>
  {
    public int numBlock;
    public int numInstr;

    public TraceLocation(int numBlock, int numInstr)
    {
      this.numBlock = numBlock;
      this.numInstr = numInstr;
    }

    public override bool Equals(object obj)
    {
      TraceLocation that = obj as TraceLocation;
      if (that == null)
      {
        return false;
      }

      return (numBlock == that.numBlock && numInstr == that.numInstr);
    }

    public bool Equals(TraceLocation that)
    {
      return (numBlock == that.numBlock && numInstr == that.numInstr);
    }

    public override int GetHashCode()
    {
      return numBlock.GetHashCode() ^ 131 * numInstr.GetHashCode();
    }
  }

  public abstract class Counterexample
  {

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Trace != null);
      Contract.Invariant(Context != null);
      Contract.Invariant(Cce.NonNullDictionaryAndValues(calleeCounterexamples));
    }

    public ProofRun ProofRun { get; }
    protected readonly VCGenOptions options;
    [Peer] public List<Block> Trace;
    public List<object> AugmentedTrace;
    public Model Model { get; }
    public ModelViewInfo MvInfo;
    public ProverContext Context;
    public abstract byte[] Checksum { get; }
    public byte[] SugaredCmdChecksum;
    public bool IsAuxiliaryCexForDiagnosingTimeouts;

    public Dictionary<TraceLocation, CalleeCounterexampleInfo> calleeCounterexamples;

    internal Counterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, Model model,
      VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun)
    {
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      this.options = options;
      this.Trace = trace;
      this.Model = model;
      this.MvInfo = mvInfo;
      this.Context = context;
      this.ProofRun = proofRun;
      this.calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
      // the call to instance method GetModelValue in the following code requires the fields Model and Context to be initialized
      if (augmentedTrace != null)
      {
        this.AugmentedTrace = augmentedTrace
          .Select(elem => elem is IdentifierExpr identifierExpr ? GetModelValue(identifierExpr.Decl) : elem).ToList();
      }
    }

    // Create a shallow copy of the counterexample
    public abstract Counterexample Clone();

    public void AddCalleeCounterexample(TraceLocation loc, CalleeCounterexampleInfo cex)
    {
      Contract.Requires(cex != null);
      calleeCounterexamples[loc] = cex;
    }

    public void AddCalleeCounterexample(int numBlock, int numInstr, CalleeCounterexampleInfo cex)
    {
      Contract.Requires(cex != null);
      calleeCounterexamples[new TraceLocation(numBlock, numInstr)] = cex;
    }

    public void AddCalleeCounterexample(Dictionary<TraceLocation, CalleeCounterexampleInfo> cs)
    {
      Contract.Requires(Cce.NonNullDictionaryAndValues(cs));
      foreach (TraceLocation loc in cs.Keys)
      {
        AddCalleeCounterexample(loc, cs[loc]);
      }
    }

    // Looks up the Cmd at a given index into the trace
    public Cmd GetTraceCmd(TraceLocation loc)
    {
      Debug.Assert(loc.numBlock < Trace.Count);
      Block b = Trace[loc.numBlock];
      Debug.Assert(loc.numInstr < b.Cmds.Count);
      return b.Cmds[loc.numInstr];
    }

    // Looks up the name of the called procedure.
    // Asserts that the name exists
    public string GetCalledProcName(Cmd cmd)
    {
      // There are two options:
      // 1. cmd is a CallCmd
      // 2. cmd is an AssumeCmd (passified version of a CallCmd)
      if (cmd is CallCmd)
      {
        return (cmd as CallCmd).Proc.Name;
      }

      AssumeCmd assumeCmd = cmd as AssumeCmd;
      Debug.Assert(assumeCmd != null);

      NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
      Debug.Assert(naryExpr != null);

      return naryExpr.Fun.FunctionName;
    }

    public void Print(int indent, TextWriter tw, Action<Block> blockAction = null)
    {
      int numBlock = -1;
      string ind = new string(' ', indent);
      foreach (Block b in Trace)
      {
        Contract.Assert(b != null);
        numBlock++;
        if (b.tok == null)
        {
          tw.WriteLine("{0}<intermediate block>", ind);
        }
        else
        {
          // for ErrorTrace == 1 restrict the output;
          // do not print tokens with -17:-4 as their location because they have been
          // introduced in the translation and do not give any useful feedback to the user
          if (!(options.ErrorTrace == 1 && b.tok.line == -17 && b.tok.col == -4))
          {
            if (blockAction != null)
            {
              blockAction(b);
            }

            tw.WriteLine("{4}{0}({1},{2}): {3}", b.tok.filename, b.tok.line, b.tok.col, b.Label, ind);

            for (int numInstr = 0; numInstr < b.Cmds.Count; numInstr++)
            {
              var loc = new TraceLocation(numBlock, numInstr);
              if (calleeCounterexamples.ContainsKey(loc))
              {
                var cmd = GetTraceCmd(loc);
                var calleeName = GetCalledProcName(cmd);
                if (calleeName.StartsWith(VC.StratifiedVerificationConditionGeneratorBase.recordProcName) &&
                    options.StratifiedInlining > 0)
                {
                  Contract.Assert(calleeCounterexamples[loc].args.Count == 1);
                  var arg = calleeCounterexamples[loc].args[0];
                  tw.WriteLine("{0}value = {1}", ind, arg.ToString());
                }
                else
                {
                  tw.WriteLine("{1}Inlined call to procedure {0} begins", calleeName, ind);
                  calleeCounterexamples[loc].counterexample.Print(indent + 4, tw);
                  tw.WriteLine("{1}Inlined call to procedure {0} ends", calleeName, ind);
                }
              }
            }
          }
        }
      }
    }

    public void PrintModel(TextWriter tw, Counterexample counterexample)
    {
      Contract.Requires(counterexample != null);

      var filenameTemplate = options.ModelViewFile;
      if (Model == null || filenameTemplate == null || options.StratifiedInlining > 0)
      {
        return;
      }
      
      if (!Model.ModelHasStatesAlready) {
        throw new InvalidOperationException("Model should have states before being printed");
      }

      if (filenameTemplate == "-")
      {
        Model.Write(tw);
        tw.Flush();
      }
      else {
        var (filename, reused) = Helpers.GetLogFilename(ProofRun.Description, filenameTemplate, true);
        using var wr = new StreamWriter(filename, reused);
        Model.Write(wr);
      }
    }

    public void InitializeModelStates()
    {
      if (Model is { ModelHasStatesAlready: false }) {
        PopulateModelWithStates(Trace, ModelFailingCommand);
        Model.ModelHasStatesAlready = true;
      }
    }

    void ApplyRedirections()
    {
      var mapping = new Dictionary<Model.Element, Model.Element>();
      foreach (var name in new string[] {"U_2_bool", "U_2_int"})
      {
        Model.Func f = Model.TryGetFunc(name);
        if (f != null && f.Arity == 1)
        {
          foreach (var ft in f.Apps)
          {
            mapping[ft.Args[0]] = ft.Result;
          }
        }
      }

      Model.Substitute(mapping);
    }

    protected abstract Cmd ModelFailingCommand { get; }

    public void PopulateModelWithStates(List<Block> trace, Cmd/*?*/ failingCmd)
    {
      Contract.Requires(Model != null);
      Contract.Requires(trace != null);

      Model m = Model;
      ApplyRedirections();

      if (MvInfo == null) {
        return;
      }

      foreach (Variable v in MvInfo.AllVariables)
      {
        m.InitialState.AddBinding(v.Name, GetModelValue(v));
      }

      var prevInc = new Dictionary<Variable, Expr>();
      for (int i = 0; i < trace.Count; ++i)
      {
        if (!MvInfo.BlockToCapturePointIndex.TryGetValue(trace[i], out var points)) {
          continue;
        }
        int cmdIndexlimit;
        if (i < trace.Count - 1 || failingCmd == null) {
          cmdIndexlimit = trace[i].Cmds.Count;
        } else {
          // this is the last block, so we only want to consider :captureState markers before
          // the error
          for (cmdIndexlimit = 0; cmdIndexlimit < trace[i].Cmds.Count; cmdIndexlimit++) {
            var cmd = trace[i].Cmds[cmdIndexlimit];
            if (cmd is AssertRequiresCmd arc && arc.Call == failingCmd) {
              break;
            } else if (cmd == failingCmd) {
              break;
            }
          }
        }
        var index = 0;
        foreach (var (captureStateAssumeCmd, map) in points) {
          if (i == trace.Count - 1 && failingCmd != null) {
            // Don't go past the error in this block
            // Continue looking through the commands in block trace[i] to see which one we'll
            // find next, the capture-state command or the error command.
            for (; index < trace[i].Cmds.Count; index++) {
              var cmd = trace[i].Cmds[index];
              if (cmd == captureStateAssumeCmd) {
                // yes, include MvInfo.CapturePoints[capturePointIndex]
                break;
              } else if ((cmd is AssertRequiresCmd arc && arc.Call == failingCmd) || cmd == failingCmd) {
                // don't include any further captured points
                return;
              }
            }
          }
          
          var cs = m.MkState(map.Description);

          foreach (Variable v in MvInfo.AllVariables)
          {
            if (!map.IncarnationMap.TryGetValue(v, out var e)) {
              continue; // not in the current state
            }
            Contract.Assert(e != null);

            if (prevInc.TryGetValue(v, out var prevIncV) && e == prevIncV) {
              continue; // skip unchanged variables
            }

            Model.Element elt;
            if (e is IdentifierExpr ide)
            {
              elt = GetModelValue(ide.Decl);
            }
            else if (e is LiteralExpr lit)
            {
              elt = m.MkElement(lit.Val.ToString());
            }
            else
            {
              elt = m.MkFunc(e.ToString(), 0).GetConstant();
            }

            cs.AddBinding(v.Name, elt);
          }

          prevInc = map.IncarnationMap;
        }
      }
    }

    public Model.Element GetModelValue(Variable v)
    {
      Model.Element elt;
      // first, get the unique name
      string uniqueName;
      VCExprVar vvar = Context.BoogieExprTranslator.TryLookupVariable(v);
      if (vvar == null)
      {
        uniqueName = v.Name;
      }
      else
      {
        uniqueName = Context.Lookup(vvar);
      }

      var f = Model.TryGetFunc(uniqueName);
      if (f == null)
      {
        f = Model.MkFunc(uniqueName, 0);
      }

      elt = f.GetConstant();
      return elt;
    }

    public abstract int GetLocation();

    public ErrorInformation CreateErrorInformation(VcOutcome vcOutcome, bool forceBplErrors)
    {
      ErrorInformation errorInfo;
      var cause = vcOutcome switch {
        VcOutcome.TimedOut => "Timed out on",
        VcOutcome.OutOfMemory => "Out of memory on",
        VcOutcome.SolverException => "Solver exception on",
        VcOutcome.OutOfResource => "Out of resource on",
        _ => "Error"
      };

      if (this is CallCounterexample callError)
      {
        if (callError.FailingRequires.ErrorMessage == null || forceBplErrors)
        {
          string msg = callError.FailingCall.Description.FailureDescription;
          errorInfo = ErrorInformation.Create(callError.FailingCall.tok, msg, cause);
          errorInfo.Kind = ErrorKind.Precondition;
          errorInfo.AddAuxInfo(callError.FailingRequires.tok,
            callError.FailingRequires.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = ErrorInformation.Create(null, callError.FailingRequires.ErrorMessage, null);
        }
      }
      else if (this is ReturnCounterexample returnError)
      {
        if (returnError.FailingEnsures.ErrorMessage == null || forceBplErrors)
        {
          errorInfo = ErrorInformation.Create(returnError.FailingReturn.tok, returnError.FailingReturn.Description.FailureDescription, cause);
          errorInfo.Kind = ErrorKind.Postcondition;
          errorInfo.AddAuxInfo(returnError.FailingEnsures.tok,
            returnError.FailingEnsures.Description.FailureDescription,
            "Related location");
        }
        else
        {
          errorInfo = ErrorInformation.Create(null, returnError.FailingEnsures.ErrorMessage, null);
        }
      }
      else // error is AssertCounterexample
      {
        var assertError = (AssertCounterexample)this;
        var failingAssert = assertError.FailingAssert;
        if (failingAssert is LoopInitAssertCmd or LoopInvMaintainedAssertCmd)
        {
          errorInfo = ErrorInformation.Create(failingAssert.tok, failingAssert.Description.FailureDescription, cause);
          errorInfo.Kind = failingAssert is LoopInitAssertCmd ?
            ErrorKind.InvariantEntry : ErrorKind.InvariantMaintainance;
          string relatedMessage = null;
          if (failingAssert is LoopInitAssertCmd initCmd)
          {
            var desc = initCmd.originalAssert.Description;
            if (desc is not AssertionDescription)
            {
              relatedMessage = desc.FailureDescription;
            }
          }
          else if (failingAssert is LoopInvMaintainedAssertCmd maintCmd)
          {
            var desc = maintCmd.originalAssert.Description;
            if (desc is not AssertionDescription)
            {
              relatedMessage = desc.FailureDescription;
            }
          }

          if (relatedMessage != null) {
            errorInfo.AddAuxInfo(failingAssert.tok, relatedMessage, "Related message");
          }
        }
        else
        {
          if (failingAssert.ErrorMessage == null || forceBplErrors)
          {
            string msg = failingAssert.Description.FailureDescription;
            errorInfo = ErrorInformation.Create(failingAssert.tok, msg, cause);
            errorInfo.Kind = ErrorKind.Assertion;
          }
          else
          {
            errorInfo = ErrorInformation.Create(null, failingAssert.ErrorMessage, null);
          }
        }
      }

      return errorInfo;
    }
  }

  public class CounterexampleComparer : IComparer<Counterexample>, IEqualityComparer<Counterexample>
  {
    private int Compare(List<Block> bs1, List<Block> bs2)
    {
      if (bs1.Count < bs2.Count)
      {
        return -1;
      }
      else if (bs2.Count < bs1.Count)
      {
        return 1;
      }

      for (int i = 0; i < bs1.Count; i++)
      {
        var b1 = bs1[i];
        var b2 = bs2[i];
        if (b1.tok.pos < b2.tok.pos)
        {
          return -1;
        }
        else if (b2.tok.pos < b1.tok.pos)
        {
          return 1;
        }
      }

      return 0;
    }

    public int Compare(Counterexample c1, Counterexample c2)
    {
      //Contract.Requires(c1 != null);
      //Contract.Requires(c2 != null);
      if (c1.GetLocation() == c2.GetLocation())
      {
        var c = Compare(c1.Trace, c2.Trace);
        if (c != 0)
        {
          return c;
        }

        // TODO(wuestholz): Generalize this to compare all Descriptions of the counterexample.
        var a1 = c1 as AssertCounterexample;
        var a2 = c2 as AssertCounterexample;
        if (a1 != null && a2 != null) {
          var s1 = a1.FailingAssert.Description?.FailureDescription;
          var s2 = a2.FailingAssert.Description?.FailureDescription;
          if (s1 != null && s2 != null)
          {
            return s1.CompareTo(s2);
          }
        }

        return 0;
      }

      if (c1.GetLocation() > c2.GetLocation())
      {
        return 1;
      }

      return -1;
    }

    public bool Equals(Counterexample x, Counterexample y)
    {
      return Compare(x, y) == 0;
    }

    public int GetHashCode(Counterexample obj)
    {
      return 0;
    }
  }

  public class AssertCounterexample : Counterexample
  {
    [Peer] public AssertCmd FailingAssert;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(FailingAssert != null);
    }


    public AssertCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertCmd failingAssert, Model model, VC.ModelViewInfo mvInfo,
      ProverContext context, ProofRun proofRun)
      : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun)
    {
      Contract.Requires(trace != null);
      Contract.Requires(failingAssert != null);
      Contract.Requires(context != null);
      this.FailingAssert = failingAssert;
    }

    protected override Cmd ModelFailingCommand => FailingAssert;

    public override int GetLocation()
    {
      return FailingAssert.tok.line * 1000 + FailingAssert.tok.col;
    }

    public override byte[] Checksum
    {
      get { return FailingAssert.Checksum; }
    }

    public override Counterexample Clone()
    {
      var ret = new AssertCounterexample(options, Trace, AugmentedTrace, FailingAssert, Model, MvInfo, Context, ProofRun);
      ret.calleeCounterexamples = calleeCounterexamples;
      return ret;
    }
  }

  public class CallCounterexample : Counterexample
  {
    public CallCmd FailingCall;
    public Requires FailingRequires;
    public AssertRequiresCmd FailingAssert;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(FailingCall != null);
      Contract.Invariant(FailingRequires != null);
    }


    public CallCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertRequiresCmd assertRequiresCmd, Model model,
      VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun, byte[] checksum = null)
      : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun)
    {
      var failingRequires = assertRequiresCmd.Requires;
      var failingCall = assertRequiresCmd.Call;
      Contract.Requires(!failingRequires.Free);
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Requires(failingCall != null);
      Contract.Requires(failingRequires != null);
      this.FailingCall = failingCall;
      this.FailingRequires = failingRequires;
      this.FailingAssert = assertRequiresCmd;
      this.checksum = checksum;
      this.SugaredCmdChecksum = failingCall.Checksum;
    }

    protected override Cmd ModelFailingCommand => FailingCall;

    public override int GetLocation()
    {
      return FailingCall.tok.line * 1000 + FailingCall.tok.col;
    }

    byte[] checksum;

    public override byte[] Checksum
    {
      get { return checksum; }
    }

    public override Counterexample Clone()
    {
      var ret = new CallCounterexample(options, Trace, AugmentedTrace, FailingAssert, Model, MvInfo, Context, ProofRun, Checksum);
      ret.calleeCounterexamples = calleeCounterexamples;
      return ret;
    }
  }

  public class ReturnCounterexample : Counterexample
  {
    public TransferCmd FailingReturn;
    public Ensures FailingEnsures;
    public AssertEnsuresCmd FailingAssert;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(FailingEnsures != null);
      Contract.Invariant(FailingReturn != null);
    }


    public ReturnCounterexample(VCGenOptions options, List<Block> trace, List<object> augmentedTrace, AssertEnsuresCmd assertEnsuresCmd, TransferCmd failingReturn, Model model,
      VC.ModelViewInfo mvInfo, ProverContext context, ProofRun proofRun, byte[] checksum)
      : base(options, trace, augmentedTrace, model, mvInfo, context, proofRun)
    {
      var failingEnsures = assertEnsuresCmd.Ensures;
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Requires(failingReturn != null);
      Contract.Requires(failingEnsures != null);
      Contract.Requires(!failingEnsures.Free);
      this.FailingReturn = failingReturn;
      this.FailingEnsures = failingEnsures;
      this.FailingAssert = assertEnsuresCmd;
      this.checksum = checksum;
    }

    protected override Cmd ModelFailingCommand => null;

    public override int GetLocation()
    {
      return FailingReturn.tok.line * 1000 + FailingReturn.tok.col;
    }

    byte[] checksum;

    /// <summary>
    /// Returns the checksum of the corresponding assertion.
    /// </summary>
    public override byte[] Checksum
    {
      get { return checksum; }
    }

    public override Counterexample Clone()
    {
      var ret = new ReturnCounterexample(options, Trace, AugmentedTrace, FailingAssert, FailingReturn, Model, MvInfo, Context, ProofRun, checksum);
      ret.calleeCounterexamples = calleeCounterexamples;
      return ret;
    }
  }

  public class VerifierCallback
  {
    private CoreOptions.ProverWarnings printProverWarnings;

    public VerifierCallback(CoreOptions.ProverWarnings printProverWarnings)
    {
      this.printProverWarnings = printProverWarnings;
    }

    // reason == null means this is genuine counterexample returned by the prover
    // other reason means it's time out/memory out/crash
    public virtual void OnCounterexample(Counterexample ce, string /*?*/ reason)
    {
      Contract.Requires(ce != null);
    }

    // called in case resource is exceeded and we don't have counterexample
    public virtual void OnTimeout(string reason)
    {
      Contract.Requires(reason != null);
    }

    public virtual void OnOutOfMemory(string reason)
    {
      Contract.Requires(reason != null);
    }

    public virtual void OnOutOfResource(string reason)
    {
      Contract.Requires(reason != null);
    }

    public delegate void ProgressDelegate(string phase, int step, int totalSteps, double progressEstimate);
    
    public virtual ProgressDelegate OnProgress => null;

    public virtual void OnUnreachableCode(ImplementationRun run)
    {
      Contract.Requires(run != null);
    }

    public virtual void OnWarning(CoreOptions options, string msg)
    {
      Contract.Requires(msg != null);
      switch (printProverWarnings)
      {
        case CoreOptions.ProverWarnings.None:
          break;
        case CoreOptions.ProverWarnings.Stdout:
          options.OutputWriter.WriteLine("Prover warning: " + msg);
          break;
        case CoreOptions.ProverWarnings.Stderr:
          Console.Error.WriteLine("Prover warning: " + msg);
          break;
        default:
          Contract.Assume(false);
          throw new Cce.UnreachableException(); // unexpected case
      }
    }

    public virtual void OnVCResult(VerificationRunResult result)
    {
      Contract.Requires(result != null);
    }
  }
}
