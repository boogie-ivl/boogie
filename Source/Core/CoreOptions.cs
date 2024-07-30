using System.Collections.Generic;
using System.IO;

namespace Microsoft.Boogie
{
  /// <summary>
  /// Boogie command-line options (other tools can subclass this class in order to support a
  /// superset of Boogie's options).
  /// </summary>
  public interface CoreOptions : PrintOptions {
    public TextWriter OutputWriter { get; }

    public enum TypeEncoding
    {
      Predicates,
      Arguments,
      Monomorphic
    }

    public enum InstrumentationPlaces
    {
      LoopHeaders,
      Everywhere
    }

    // whether procedure inlining is enabled at call sites.
    public enum Inlining
    {
      None,
      Assert,
      Assume,
      Spec
    }

    public Inlining ProcedureInlining { get; set; }

    public bool Trace { get; }

    public enum VerbosityLevel
    {
      Silent,
      Quiet,
      Normal,
      Trace
    }

    public VerbosityLevel Verbosity { get; set; }

    public bool TraceVerify { get; }

    public int VerifySnapshots { get; }
    string VersionNumber { get; }
    bool OverlookBoogieTypeErrors { get; }
    uint TimeLimit { get; }
    uint ResourceLimit { get; }
    bool DoModSetAnalysis { get; }
    bool DebugStagedHoudini { get; }
    bool DeterministicExtractLoops { get; }
    string VariableDependenceIgnore { get; }
    bool PruneInfeasibleEdges { get; }
    bool ModifyTopologicalSorting { get; }
    bool ExtractLoopsUnrollIrreducible { get; }
    int RecursionBound { get; }
    int InlineDepth { get; }
    bool TraceTimes { get; }
    bool FreeVarLambdaLifting { get; }
    InstrumentationPlaces InstrumentInfer { get; }
    AiFlags Ai { get; }
    bool InstrumentWithAsserts { get; }
    bool UseArrayTheory { get; }
    TypeEncoding TypeEncodingMethod { get; set; }
    SubsumptionOption UseSubsumption { get; }
    int VcsCores { get; }
    int RandomizeVcIterations { get; }
    List<string> ProverOptions { get; }
    bool Prune { get; }
    bool RunDiagnosticsOnTimeout { get; }
    string ProverLogFilePath { get; set; }
    bool ProverLogFileAppend { get; }
    int? RandomSeed { get; }
    int VcsMaxSplits { get; }
    int VcsMaxKeepGoingSplits { get; }
    double VcsMaxCost { get; }
    bool VcsSplitOnEveryAssert { get; }
    string PrintSplitFile { get; }
    bool PrintSplitDeclarations { get; }
    bool PrettyPrint { get; }
    bool NormalizeDeclarationOrder { get; }
    XmlSink XmlSink { get; }
    uint VcsFinalAssertTimeout { get; }
    uint VcsKeepGoingTimeout { get; }
    int ErrorLimit { get; set; }
    List<ConcurrentHoudiniOptions> Cho { get; }
    double VcsPathSplitMult { get; }
    ProverWarnings PrintProverWarnings { get; }
    bool TraceCachingForDebugging { get; }
    double VcsAssumeMult { get; }
    double VcsPathCostMult { get; }
    bool TraceCachingForTesting { get; }
    bool TraceCachingForBenchmarking { get; }
    string ModelViewFile { get; }
    int ErrorTrace { get; }
    bool RelaxFocus { get; }
    bool VcsDumpSplits { get; }
    bool SoundnessSmokeTest { get; }
    uint SmokeTimeout { get; }
    bool ConcurrentHoudini { get; }
    double VcsPathJoinMult { get; }
    bool VerifySeparately { get; }
    bool KeepQuantifier { get; }

    public enum ProverWarnings
    {
      None,
      Stdout,
      Stderr
    }
    
    public class ConcurrentHoudiniOptions
    {
      public List<string> ProverOptions = new List<string>();
      public int ErrorLimit = 5;
      public bool DisableLoopInvEntryAssert = false;
      public bool DisableLoopInvMaintainedAssert = false;
      public bool ModifyTopologicalSorting = false;
    }

    public class AiFlags
    {
      public bool J_Trivial = false;
      public bool J_Intervals = false;

      public int /*0..9*/
        StepsBeforeWidening = 0;

      public bool DebugStatistics = false;
    }

    public enum SubsumptionOption
    {
      Never,
      NotForQuantifiers,
      Always
    }
  }
}
