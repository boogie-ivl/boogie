using System;
using System.Collections.Generic;
using System.Collections.Specialized;
using System.Diagnostics.Contracts;
using System.IO;
using Microsoft.Boogie.LeanAuto;
using Microsoft.Boogie.SMTLib;
using VC;

namespace Microsoft.Boogie
{
  /// <summary>
  /// Boogie command-line options (other tools can subclass this class in order to support a
  /// superset of Boogie's options).
  /// </summary>
  public class CommandLineOptions : CommandLineOptionEngine, ExecutionEngineOptions
  {
    public static CommandLineOptions FromArguments(TextWriter outputWriter, params string[] arguments)
    {
      return FromArguments(outputWriter, new ConsolePrinter(), arguments);
    }

    public static CommandLineOptions FromArguments(TextWriter outputWriter, OutputPrinter printer, params string[] arguments) {
      var result = new CommandLineOptions(outputWriter, printer);
      result.Parse(arguments);
      return result;
    }

    public CommandLineOptions(TextWriter outputWriter, OutputPrinter printer)
      : this(outputWriter, "Boogie", "Boogie program verifier", printer)
    {
    }

    protected CommandLineOptions(TextWriter outputWriter, string toolName, string descriptiveName, OutputPrinter printer)
      : base(toolName, descriptiveName, outputWriter)
    {
      Contract.Requires(outputWriter != null);
      Contract.Requires(toolName != null);
      Contract.Requires(descriptiveName != null);
      Contract.Requires(printer.Options == null);
      Printer = printer;
      printer.Options = this;
    }

    // Flags and arguments

    public bool ExpectingModel => PrintErrorModel >= 1 ||
                                  EnhancedErrorMessages == 1 ||
                                  ModelViewFile != null ||
                                  StratifiedInlining > 0 && !StratifiedInliningWithoutModels;

    public bool ProduceModel => ExplainHoudini || UseProverEvaluate || ExpectingModel;

    public bool RunningBoogieFromCommandLine { get; set; }

    [ContractInvariantMethod]
    void ObjectInvariant2()
    {
      Contract.Invariant(LogPrefix != null);
      Contract.Invariant(0 <= PrintUnstructured &&
                         PrintUnstructured <
                         3); // 0 = print only structured,  1 = both structured and unstructured,  2 = only unstructured
    }

    public int VerifySnapshots { get; set; } = -1;
    public bool VerifySeparately { get; set; }
    public string PrintFile { get; set; }
    public string PrintSplitFile { get; set; }
    public bool PrintSplitDeclarations { get; set; }

    /**
     * Whether to emit {:qid}, {:skolemid} and set-info :boogie-vc-id
     */
    public bool EmitDebugInformation
    {
      get => emitDebugInformation;
      set => emitDebugInformation = value;
    }

    public int PrintUnstructured {
      get => printUnstructured;
      set => printUnstructured = value;
    }

    public bool UseBaseNameForFileName { get; set; }

    public bool PrintDesugarings {
      get => printDesugarings;
      set => printDesugarings = value;
    }

    public string PrintPassiveFile {
      get => printPassiveFile;
      set => printPassiveFile = value;
    }

    public List<Action<ExecutionEngineOptions, ProcessedProgram>> UseResolvedProgram { get; } = new();

    static void PassifyAllImplementations(ExecutionEngineOptions options, ProcessedProgram processedProgram)
    {
      // All three of these objects can be new instances because they're essentially not used by PrepareImplementation.
      var callback = new VerifierCallback(options.PrintProverWarnings);
      var checkerPool = new CheckerPool(options);
      var vcGenerator = new VerificationConditionGenerator(processedProgram.Program, checkerPool);

      foreach(var implementation in processedProgram.Program.Implementations) {
        vcGenerator.PrepareImplementation(new ImplementationRun(implementation, options.OutputWriter),
          callback, out _, out _, out _);
      }
    }

    public static void PrintPassiveProgram(ExecutionEngineOptions options, ProcessedProgram processedProgram)
    {
      options.PrintUnstructured = 1;
      PassifyAllImplementations(options, processedProgram);
      ExecutionEngine.PrintBplFile(options, options.PrintFile, processedProgram.Program, true, true, options.PrettyPrint);
    }

    public static void PrintPassiveProgramAsLean(string fileName, ExecutionEngineOptions options, ProcessedProgram processedProgram)
    {
        var writer = new StreamWriter(fileName);
        PassifyAllImplementations(options, processedProgram);
        LeanAutoGenerator.EmitPassiveProgramAsLean(options, processedProgram.Program, writer);
        writer.Close();

    }

    public bool PrintLambdaLifting { get; set; }
    public bool FreeVarLambdaLifting { get; set; }
    public string ProverLogFilePath { get; set; }
    public bool ProverLogFileAppend { get; set; }

    public bool PrintInstrumented {
      get => printInstrumented;
      set => printInstrumented = value;
    }

    public bool InstrumentWithAsserts
    {
      get;
      set;
    }
    public string ProverPreamble { get; set; }
    public bool WarnNotEliminatedVars { get; set; }

    /**
     * Pruning will remove any top-level Boogie declarations that are not accessible by the implementation that is about to be verified.
     *
     * # Why pruning?
     * Without pruning, a change to any part of a Boogie program has the potential to affect the verification of any other part of the program.
     *
     * When pruning is used, a declaration of a Boogie program can be changed with the guarantee that the verification of
     * implementations that do not depend on the modified declaration, remains unchanged.
     *
     * # How to use pruning
     * Pruning depends on the dependency graph of Boogie declarations.
     * This graph must contain both incoming and outgoing edges for axioms.
     *
     * Outgoing edges for axioms are detected automatically:
     * an axiom has an outgoing edge to each declaration that it references.
     *
     * When using pruning, you must ensure that the right incoming edges for axioms are defined.
     * The most manual method of defining incoming axiom edges is using 'uses' clauses, which are shown in the following program:
     *
     * ```
     * function F(int) returns (int) uses {
     *   axiom forall x: int :: F(x) == x * 2
     * }
     * function G(int) returns (int) uses {
     *   axiom forall x: int :: G(x) == F(x) + 1
     * }
     *
     * procedure FMultipliedByTwo(x: int)
     *   ensures F(x) - x == x
     * { }
     * ```
     *
     * When verifying FMultipliedByTwo, pruning will remove G and its axiom, but not F and its axiom.
     *
     * Axioms defined in a uses clause have an incoming edge from the clause's declaration.
     * Uses clauses can be placed on functions and constants.
     *
     * Adding the {:include_dep} attribute to an axiom will give it an incoming edge from each declaration that it references.
     * The {:include_dep} attribute is useful in a migration scenario.
     * When turning on pruning in a Boogie program with many axioms,
     * one may add {:include_dep} to all of them to prevent pruning too much,
     * and then iteratively remove {:include_dep} attributes and add uses clauses to enable pruning more.
     *
     * Apart from uses clauses and {:include_dep}, incoming edges are also created for axioms that contain triggers.
     * If a quantifier with a trigger occurs in an axiom, then no incoming edges are determined from the body of the quantifier,
     * regardless of {:include_dep} being present. However, for each trigger of the quantifier,
     * each declaration referenced in the trigger has an outgoing edge to a merge node,
     * that in turn has an outgoing edge to the axiom.
     * The merge node is traversable in the reachability analysis only if each of its incoming edges has been reached.
     *
     */
    public bool Prune { get; set; }

    public CoreOptions.InstrumentationPlaces InstrumentInfer { get; set; } = CoreOptions.InstrumentationPlaces.LoopHeaders;

    public int? RandomSeed { get; set; }

    public int RandomizeVcIterations { get; set; } = 1;

    public bool PrintWithUniqueASTIds {
      get => printWithUniqueAstIds;
      set => printWithUniqueAstIds = value;
    }

    private string XmlSinkFilename { get; set; }
    [Peer] public XmlSink XmlSink { get; set; }
    public bool Wait { get; set; }

    public bool Trace => Verbosity == CoreOptions.VerbosityLevel.Trace;

    public CoreOptions.VerbosityLevel Verbosity { get; set; } = CoreOptions.VerbosityLevel.Normal;

    public bool NormalizeNames
    {
      get => normalizeNames;
      set => normalizeNames = value;
    }

    public Func<SMTLibOptions, SMTLibSolverOptions, SMTLibSolver> CreateSolver { get; set; } = (libOptions, options) =>
    {
      return options.Solver switch
      {
        SolverKind.NoOpWithZ3Options => new NoopSolver(),
        _ => new SMTLibProcess(libOptions, options)
      };
    };

    public bool NormalizeDeclarationOrder
    {
      get => normalizeDeclarationOrder;
      set => normalizeDeclarationOrder = value;
    }

    public bool ImmediatelyAcceptCommands => StratifiedInlining > 0 || ContractInfer;

    public bool ProduceUnsatCores => TrackVerificationCoverage ||
                                     EnableUnSatCoreExtract == 1 ||
                                     ContractInfer && (UseUnsatCoreForContractInfer || ExplainHoudini);

    public bool BatchModeSolver { get; set; }

    public bool TraceTimes { get; set; }
    public bool TraceProofObligations { get; set; }

    public bool TraceCachingForTesting
    {
      get { return TraceCaching == 1 || TraceCaching == 3; }
    }

    public bool TraceCachingForBenchmarking
    {
      get { return TraceCaching == 2 || TraceCaching == 3; }
    }

    public bool TraceCachingForDebugging
    {
      get { return TraceCaching == 3; }
    }

    internal int TraceCaching { get; set; }
    public bool NoResolve { get; set; }
    public bool NoTypecheck { get; set; }
    public bool OverlookBoogieTypeErrors { get; set; }
    public bool Verify { get; set; } = true;
    public bool TraceVerify { get; set; }

    public int /*(0:3)*/
      ErrorTrace { get; set; } = 1;

    public bool IntraproceduralInfer { get; set; }= true;

    public bool ContractInfer {
      get => contractInfer;
      set => contractInfer = value;
    }

    public bool ExplainHoudini {
      get => explainHoudini;
      set => explainHoudini = value;
    }

    public bool ReverseHoudiniWorklist {
      get => reverseHoudiniWorklist;
      set => reverseHoudiniWorklist = value;
    }

    public bool ConcurrentHoudini  { get; set; }
    public bool ModifyTopologicalSorting  { get; set; }
    public bool DebugConcurrentHoudini  { get; set; }

    public bool HoudiniUseCrossDependencies {
      get => houdiniUseCrossDependencies;
      set => houdiniUseCrossDependencies = value;
    }

    public string StagedHoudini  { get; set; }
    public bool DebugStagedHoudini  { get; set; }
    public bool StagedHoudiniReachabilityAnalysis  { get; set; }
    public bool StagedHoudiniMergeIgnoredAnnotations  { get; set; }

    public int StagedHoudiniThreads {
      get => stagedHoudiniThreads;
      set => stagedHoudiniThreads = value;
    }

    public string VariableDependenceIgnore  { get; set; }

    public bool UseUnsatCoreForContractInfer {
      get => useUnsatCoreForContractInfer;
      set => useUnsatCoreForContractInfer = value;
    }

    public bool PrintAssignment  { get; set; }

    public bool TrackVerificationCoverage {
      get => trackVerificationCoverage;
      set => trackVerificationCoverage = value;
    }

    public int InlineDepth  { get; set; } = -1;

    public bool UseProverEvaluate {
      get => useProverEvaluate;
      set => useProverEvaluate = value;
    } // Use ProverInterface's Evaluate method, instead of model to get variable values

    public bool SoundnessSmokeTest  { get; set; }
    public int KInductionDepth { get; set; } = -1;
    public int EnableUnSatCoreExtract { get; set; }

    private string /*!*/ _logPrefix = "";

    public string LogPrefix
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._logPrefix;
      }
      set
      {
        Contract.Requires(value != null);
        this._logPrefix = value;
      }
    }

    public bool PrettyPrint { get; set; } = true;

    public CoreOptions.ProverWarnings PrintProverWarnings { get; set; } = CoreOptions.ProverWarnings.None;


    public CoreOptions.SubsumptionOption UseSubsumption { get; set; } = CoreOptions.SubsumptionOption.Always;

    public bool AlwaysAssumeFreeLoopInvariants { get; set; }

    public ExecutionEngineOptions.ShowEnvironment ShowEnv { get; set; } = ExecutionEngineOptions.ShowEnvironment.DuringPrint;
    public OutputPrinter Printer { get; set;  }

    public bool ShowVerifiedProcedureCount { get; set; } = true;

    [ContractInvariantMethod]
    void ObjectInvariant3()
    {
      Contract.Invariant(0 <= PrintErrorModel && PrintErrorModel <= 1);
      Contract.Invariant(0 <= EnhancedErrorMessages && EnhancedErrorMessages < 2);
      Contract.Invariant(0 <= Ai.StepsBeforeWidening && Ai.StepsBeforeWidening <= 9);
      Contract.Invariant(-1 <= this.bracketIdsInVC && this.bracketIdsInVC <= 1);
      Contract.Invariant(Cce.NonNullElements(this.ProverOptions));
    }

    public int LoopUnrollCount { get; set; } = -1; // -1 means don't unroll loops
    public bool SoundLoopUnrolling { get; set; }
    public int PrintErrorModel { get; set; }
    private string printErrorModelFile;

    public string /*?*/ ModelViewFile { get; set; }

    public int EnhancedErrorMessages {
      get => enhancedErrorMessages;
      set => enhancedErrorMessages = value;
    }

    public string PrintCFGPrefix { get; set; }
    public bool ForceBplErrors { get; set; } = false; // if true, boogie error is shown even if "msg" attribute is present

    public bool UseArrayTheory => !useArrayAxioms && TypeEncodingMethod == CoreOptions.TypeEncoding.Monomorphic;

    public bool RelaxFocus { get; set; }

    public bool RunDiagnosticsOnTimeout {
      get => runDiagnosticsOnTimeout;
      set => runDiagnosticsOnTimeout = value;
    }

    public bool TraceDiagnosticsOnTimeout {
      get => traceDiagnosticsOnTimeout;
      set => traceDiagnosticsOnTimeout = value;
    }

    public uint TimeLimitPerAssertionInPercent {
      get => timeLimitPerAssertionInPercent;
      set => timeLimitPerAssertionInPercent = value;
    }

    public bool SIBoolControlVC {
      get => siBoolControlVc;
      set => siBoolControlVc = value;
    }

    public TextWriter ModelWriter { get; private set; }

    public bool ExpandLambdas { get; set; } = true; // not useful from command line, only to be set to false programatically

    public bool DoModSetAnalysis {
      get => doModSetAnalysis;
      set => doModSetAnalysis = value;
    }

    public bool UseAbstractInterpretation { get; set; }

    public string CivlDesugaredFile { get; set; }

    public bool TrustMoverTypes {
      get => trustMoverTypes;
      set => trustMoverTypes = value;
    }

    public bool TrustNoninterference {
      get => trustNoninterference;
      set => trustNoninterference = value;
    }

    public bool TrustRefinement {
      get => trustRefinement;
      set => trustRefinement = value;
    }

    public int TrustLayersUpto { get; set; } = -1;
    
    public int TrustLayersDownto { get; set; } = int.MaxValue;

    public bool TrustSequentialization {
      get => trustSequentialization;
      set => trustSequentialization = value;
    }

    public bool RemoveEmptyBlocks { get; set; } = true;
    public bool CoalesceBlocks { get; set; } = true;
    public bool PruneInfeasibleEdges { get; set; } = true;

    [Rep] public ProverFactory TheProverFactory { get; set; }
    public string ProverDllName;

    public bool ProverHelpRequested {
      get => proverHelpRequested;
      set => proverHelpRequested = value;
    }

    public List<string> ProverOptions { get; set; } = new();

    private int bracketIdsInVC = -1; // -1 - not specified, 0 - no, 1 - yes

    public int BracketIdsInVC
    {
      get
      {
        Contract.Ensures(-1 <= Contract.Result<int>() && Contract.Result<int>() <= 1);
        return this.bracketIdsInVC;
      }
      set
      {
        Contract.Requires(-1 <= value && value <= 1);
        this.bracketIdsInVC = value;
      }
    }

    public uint TimeLimit { get; set; } = 0; // 0 means no limit
    public uint ResourceLimit { get; set; } = 0; // default to 0
    public uint SmokeTimeout { get; set; } = 10; // default to 10s

    public int ErrorLimit {
      get => errorLimit;
      set => errorLimit = value;
    } // 0 means attempt to falsify each assertion in a desugared implementation

    public bool RestartProverPerVC {
      get => restartProverPerVc;
      set => restartProverPerVc = value;
    }

    public double VcsMaxCost { get; set; } = 1.0;
    public double VcsPathJoinMult { get; set; } = 0.8;
    public double VcsPathCostMult { get; set; } = 1.0;
    public double VcsAssumeMult { get; set; } = 0.01;
    public double VcsPathSplitMult { get; set; } = 0.5; // 0.5-always, 2-rarely do path splitting
    public int VcsMaxSplits { get; set; } = 1;
    public int VcsMaxKeepGoingSplits { get; set; } = 1;
    public bool VcsSplitOnEveryAssert { get; set; } = false;
    public uint VcsFinalAssertTimeout { get; set; } = 30;
    public uint VcsKeepGoingTimeout { get; set; } = 1;
    public int VcsCores { get; set; } = 1;
    public bool VcsDumpSplits { get; set; } = false;

    public bool DebugRefuted { get; set; } = false;

    public XmlSink XmlRefuted
    {
      get
      {
        if (DebugRefuted)
        {
          return XmlSink;
        }
        else
        {
          return null;
        }
      }
    }

    public CoreOptions.Inlining ProcedureInlining { get; set; } = CoreOptions.Inlining.Assume;

    public bool PrintInlined {
      get => printInlined;
      set => printInlined = value;
    }

    public bool ExtractLoops { get; set; } = false;
    public bool DeterministicExtractLoops { get; set; } = false;

    // Enables VC generation for Stratified Inlining.
    // Set programmatically by Corral.
    public int StratifiedInlining  { get; set; } = 0;

    // disable model generation, used by Corral/SI
    public bool StratifiedInliningWithoutModels { get; set; }

    // Sets the recursion bound, used for loop extraction, etc.
    public int RecursionBound { get; set; } = 500;

    public bool ExtractLoopsUnrollIrreducible { get; set; } = true; // unroll irreducible loops? (set programmatically)

    public CoreOptions.TypeEncoding TypeEncodingMethod { get; set; } = CoreOptions.TypeEncoding.Monomorphic;

    public bool ReflectAdd { get; set; } = false;

    public int LiveVariableAnalysis { get; set; } = 1;

    public bool KeepQuantifier {
      get => keepQuantifier;
      set => keepQuantifier = value;
    }

    public HashSet<string> Libraries { get; set; } = new HashSet<string>();

    // Note that procsToCheck stores all patterns <p> supplied with /proc:<p>
    // (and similarly procsToIgnore for /noProc:<p>). Thus, if procsToCheck
    // is empty it means that all procedures should be checked.
    public List<string> ProcsToCheck { get; set; } = new();
    public List<string /*!*/> ProcsToIgnore { get; set; } = new();

    [ContractInvariantMethod]
    void ObjectInvariant5()
    {
      Contract.Invariant(Cce.NonNullElements(this.ProcsToCheck, true));
      Contract.Invariant(Cce.NonNullElements(this.ProcsToIgnore, true));
      Contract.Invariant(Ai != null);
    }

    public CoreOptions.AiFlags /*!*/ Ai  { get; private set; } = new();

    private bool proverHelpRequested = false;
    private bool restartProverPerVc = false;
    private bool useArrayAxioms = false;
    private bool doModSetAnalysis = false;
    private bool runDiagnosticsOnTimeout = false;
    private bool traceDiagnosticsOnTimeout = false;
    private bool siBoolControlVc = false;
    private bool contractInfer = false;
    private bool explainHoudini = false;
    private bool reverseHoudiniWorklist = false;
    private bool houdiniUseCrossDependencies = false;
    private bool useUnsatCoreForContractInfer = false;
    private bool trackVerificationCoverage = false;
    private bool useProverEvaluate;
    private bool trustMoverTypes = false;
    private bool trustNoninterference = false;
    private bool trustRefinement = false;
    private bool trustSequentialization = false;
    private int enhancedErrorMessages = 0;
    private int stagedHoudiniThreads = 1;
    private uint timeLimitPerAssertionInPercent = 10;
    private int errorLimit = 5;
    private bool printInlined = false;
    private bool printInstrumented = false;
    private bool printWithUniqueAstIds = false;
    private int printUnstructured = 0;
    private bool printDesugarings = false;
    private string printPassiveFile;
    private bool emitDebugInformation = true;
    private bool normalizeNames;
    private bool normalizeDeclarationOrder = true;
    private bool keepQuantifier = false;

    public List<CoreOptions.ConcurrentHoudiniOptions> Cho { get; set; } = new();

    protected override bool ParseOption(string name, CommandLineParseState ps)
    {
      var args = ps.args; // convenient synonym
      switch (name)
      {
        case "infer":
          if (ps.ConfirmArgumentCount(1))
          {
            UseAbstractInterpretation = true;
            foreach (char c in Cce.NonNull(args[ps.i]))
            {
              switch (c)
              {
                case 't':
                  Ai.J_Trivial = true;
                  break;
                case 'j':
                  Ai.J_Intervals = true;
                  break;
                case 's':
                  Ai.DebugStatistics = true;
                  break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                  Ai.StepsBeforeWidening = (int) char.GetNumericValue(c);
                  break;
                default:
                  ps.Error("Invalid argument '{0}' to option {1}", c.ToString(), ps.s);
                  break;
              }
            }

            if (Ai.J_Trivial == Ai.J_Intervals)
            {
              ps.Error("Option {0} requires the selection of exactly one abstract domain", ps.s);
            }
          }

          return true;

        case "break":
        case "launch":
          if (ps.ConfirmArgumentCount(0))
          {
            System.Diagnostics.Debugger.Launch();
          }

          return true;

        case "lib":
          if (ps.ConfirmArgumentCount(1))
          {
            this.Libraries.Add(Cce.NonNull(args[ps.i]));
          }

          return true;

        case "proc":
          if (ps.ConfirmArgumentCount(1))
          {
            this.ProcsToCheck.Add(Cce.NonNull(args[ps.i]));
          }

          return true;

        case "noProc":
          if (ps.ConfirmArgumentCount(1))
          {
            this.ProcsToIgnore.Add(Cce.NonNull(args[ps.i]));
          }

          return true;

        case "xml":
          if (ps.ConfirmArgumentCount(1))
          {
            XmlSinkFilename = args[ps.i];
          }

          return true;

        case "printPruned":
        case "printSplit":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintSplitFile = args[ps.i];
          }

          return true;
        case "printSplitDeclarations":
          if (ps.ConfirmArgumentCount(0))
          {
            PrintSplitDeclarations = true;
          }

          return true;
        
        case "printPassive":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintPassiveFile = args[ps.i];
          }

          return true;
        
        case "print":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintFile = args[ps.i];
          }

          return true;

        case "printLean":
          if (ps.ConfirmArgumentCount(1)) {
            var fileName = args[ps.i];
            UseResolvedProgram.Add((o, p) =>
              PrintPassiveProgramAsLean(fileName, o, p));
          }

          return true;

        case "pretty":
          int val = 1;
          if (ps.GetIntArgument(x => val = x, 2))
          {
            PrettyPrint = val == 1;
          }

          return true;

        case "civlDesugaredFile":
          if (ps.ConfirmArgumentCount(1))
          {
            CivlDesugaredFile = args[ps.i];
          }

          return true;

        case "trustLayersUpto":
          if (ps.ConfirmArgumentCount(1))
          {
            ps.GetIntArgument(x => TrustLayersUpto = x);
          }

          return true;

        case "trustLayersDownto":
          if (ps.ConfirmArgumentCount(1))
          {
            ps.GetIntArgument(x => TrustLayersDownto = x);
          }

          return true;

        case "proverLog":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverLogFilePath = args[ps.i];
          }

          return true;

        case "proverPreamble":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverPreamble = args[ps.i];
          }

          return true;

        case "logPrefix":
          if (ps.ConfirmArgumentCount(1))
          {
            string s = Cce.NonNull(args[ps.i]);
            LogPrefix += s.Replace('/', '-').Replace('\\', '-');
          }

          return true;

        case "errorTrace":
          ps.GetIntArgument(x => ErrorTrace = x, 3);
          return true;

        case "proverWarnings":
        {
          int pw = 0;
          if (ps.GetIntArgument(x => pw = x, 3))
          {
            switch (pw)
            {
              case 0:
                PrintProverWarnings = CoreOptions.ProverWarnings.None;
                break;
              case 1:
                PrintProverWarnings = CoreOptions.ProverWarnings.Stdout;
                break;
              case 2:
                PrintProverWarnings = CoreOptions.ProverWarnings.Stderr;
                break;
              default:
              {
                Contract.Assert(false);
                throw new Cce.UnreachableException();
              } // postcondition of GetIntArgument guarantees that we don't get here
            }
          }

          return true;
        }

        case "env":
        {
          int e = 0;
          if (ps.GetIntArgument(x => e = x, 3))
          {
            switch (e)
            {
              case 0:
                ShowEnv = ExecutionEngineOptions.ShowEnvironment.Never;
                break;
              case 1:
                ShowEnv = ExecutionEngineOptions.ShowEnvironment.DuringPrint;
                break;
              case 2:
                ShowEnv = ExecutionEngineOptions.ShowEnvironment.Always;
                break;
              default:
              {
                Contract.Assert(false);
                throw new Cce.UnreachableException();
              } // postcondition of GetIntArgument guarantees that we don't get here
            }
          }

          return true;
        }

        case "printVerifiedProceduresCount":
        {
          int n = 0;
          if (ps.GetIntArgument(x => n = x, 2))
          {
            ShowVerifiedProcedureCount = n != 0;
          }

          return true;
        }

        case "loopUnroll":
          ps.GetIntArgument(x => LoopUnrollCount = x);
          return true;

        case "printModel":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "0":
                PrintErrorModel = 0;
                break;
              case "1":
                PrintErrorModel = 1;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;

        case "mv":
          if (ps.ConfirmArgumentCount(1))
          {
            ModelViewFile = args[ps.i];
          }

          return true;

        case "printModelToFile":
          if (ps.ConfirmArgumentCount(1))
          {
            printErrorModelFile = args[ps.i];
          }

          return true;

        case "enhancedErrorMessages":
          ps.GetIntArgument(x => enhancedErrorMessages = x, 2);
          return true;

        case "printCFG":
          if (ps.ConfirmArgumentCount(1))
          {
            PrintCFGPrefix = args[ps.i];
          }

          return true;

        case "inlineDepth":
          ps.GetIntArgument(x => InlineDepth = x);
          return true;

        case "subsumption":
        {
          int s = 0;
          if (ps.GetIntArgument(x => s = x, 3))
          {
            switch (s)
            {
              case 0:
                UseSubsumption = CoreOptions.SubsumptionOption.Never;
                break;
              case 1:
                UseSubsumption = CoreOptions.SubsumptionOption.NotForQuantifiers;
                break;
              case 2:
                UseSubsumption = CoreOptions.SubsumptionOption.Always;
                break;
              default:
              {
                Contract.Assert(false);
                throw new Cce.UnreachableException();
              } // postcondition of GetIntArgument guarantees that we don't get here
            }
          }

          return true;
        }

        case "liveVariableAnalysis":
        {
          int lva = 0;
          if (ps.GetIntArgument(x => lva = x, 3))
          {
            LiveVariableAnalysis = lva;
          }

          return true;
        }

        case "removeEmptyBlocks":
        {
          int reb = 0;
          if (ps.GetIntArgument(x => reb = x, 2))
          {
            RemoveEmptyBlocks = reb == 1;
          }

          return true;
        }

        case "coalesceBlocks":
        {
          int cb = 0;
          if (ps.GetIntArgument(x => cb = x, 2))
          {
            CoalesceBlocks = cb == 1;
          }

          return true;
        }

        case "noPruneInfeasibleEdges":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            PruneInfeasibleEdges = false;
          }

          return true;
        }

        case "stagedHoudini":
        {
          if (ps.ConfirmArgumentCount(1))
          {
            if (args[ps.i] == "COARSE" ||
                args[ps.i] == "FINE" ||
                args[ps.i] == "BALANCED")
            {
              StagedHoudini = args[ps.i];
            }
            else
            {
              ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
            }
          }

          return true;
        }

        case "stagedHoudiniThreads":
        {
          ps.GetIntArgument(x => stagedHoudiniThreads = x);
          return true;
        }

        case "stagedHoudiniReachabilityAnalysis":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            StagedHoudiniReachabilityAnalysis = true;
          }

          return true;
        }

        case "stagedHoudiniMergeIgnoredAnnotations":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            StagedHoudiniMergeIgnoredAnnotations = true;
          }

          return true;
        }

        case "debugStagedHoudini":
        {
          if (ps.ConfirmArgumentCount(0))
          {
            DebugStagedHoudini = true;
          }

          return true;
        }

        case "variableDependenceIgnore":
        {
          if (ps.ConfirmArgumentCount(1))
          {
            VariableDependenceIgnore = args[ps.i];
          }

          return true;
        }

        case "proverDll":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverDllName = Cce.NonNull(args[ps.i]);
            TheProverFactory = ProverFactory.Load(ProverDllName);
          }

          return true;

        case "p":
        case "proverOpt":
          if (ps.ConfirmArgumentCount(1))
          {
            ProverOptions.Add(Cce.NonNull(args[ps.i]));
          }

          return true;

        case "extractLoops":
          if (ps.ConfirmArgumentCount(0))
          {
            ExtractLoops = true;
          }

          return true;

        case "deterministicExtractLoops":
          if (ps.ConfirmArgumentCount(0))
          {
            DeterministicExtractLoops = true;
          }

          return true;

        case "inline":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "none":
                ProcedureInlining = CoreOptions.Inlining.None;
                break;
              case "assert":
                ProcedureInlining = CoreOptions.Inlining.Assert;
                break;
              case "assume":
                ProcedureInlining = CoreOptions.Inlining.Assume;
                break;
              case "spec":
                ProcedureInlining = CoreOptions.Inlining.Spec;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;
        case "recursionBound":
          if (ps.ConfirmArgumentCount(1))
          {
            RecursionBound = Int32.Parse(Cce.NonNull(args[ps.i]));
          }

          return true;
        case "enableUnSatCoreExtraction":
          if (ps.ConfirmArgumentCount(1))
          {
            EnableUnSatCoreExtract = Int32.Parse(Cce.NonNull(args[ps.i]));
          }

          return true;

        case "typeEncoding":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "m":
              case "monomorphic":
                TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
                break;
              case "p":
              case "predicates":
                TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates;
                break;
              case "a":
              case "arguments":
                TypeEncodingMethod = CoreOptions.TypeEncoding.Arguments;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;

        case "instrumentInfer":
          if (ps.ConfirmArgumentCount(1))
          {
            switch (args[ps.i])
            {
              case "e":
                InstrumentInfer = CoreOptions.InstrumentationPlaces.Everywhere;
                break;
              case "h":
                InstrumentInfer = CoreOptions.InstrumentationPlaces.LoopHeaders;
                break;
              default:
                ps.Error("Invalid argument \"{0}\" to option {1}", args[ps.i], ps.s);
                break;
            }
          }

          return true;

        case "concurrentHoudini":
          if (ps.ConfirmArgumentCount(0))
          {
            ConcurrentHoudini = true;
          }

          return true;

        case "modifyTopologicalSorting":
          if (ps.ConfirmArgumentCount(0))
          {
            ModifyTopologicalSorting = true;
          }

          return true;

        case "debugConcurrentHoudini":
          if (ps.ConfirmArgumentCount(0))
          {
            DebugConcurrentHoudini = true;
          }

          return true;

        case "vcBrackets":
          ps.GetIntArgument(x => bracketIdsInVC = x, 2);
          return true;

        case "vcsMaxCost":
          ps.GetDoubleArgument(x => VcsMaxCost = x);
          return true;

        case "vcsPathJoinMult":
          ps.GetDoubleArgument(x => VcsPathJoinMult = x);
          return true;

        case "vcsPathCostMult":
          ps.GetDoubleArgument(x => VcsPathCostMult = x);
          return true;

        case "vcsAssumeMult":
          ps.GetDoubleArgument(x => VcsAssumeMult = x);
          return true;

        case "vcsPathSplitMult":
          ps.GetDoubleArgument(x => VcsPathSplitMult = x);
          return true;

        case "vcsMaxSplits":
          ps.GetIntArgument(x => VcsMaxSplits = x);
          return true;

        case "vcsMaxKeepGoingSplits":
          ps.GetIntArgument(x => VcsMaxKeepGoingSplits = x);
          return true;

        case "vcsSplitOnEveryAssert":
          if (ps.ConfirmArgumentCount(0))
          {
            VcsSplitOnEveryAssert = true;
          }
          return true;

        case "vcsFinalAssertTimeout":
          ps.GetUnsignedNumericArgument(x => VcsFinalAssertTimeout = x);
          return true;

        case "vcsKeepGoingTimeout":
          ps.GetUnsignedNumericArgument(x => VcsKeepGoingTimeout = x);
          return true;

        case "vcsCores":
          ps.GetIntArgument(x => VcsCores = x, a => 1 <= a);
          return true;

        case "randomSeedIterations": // old name of the option that should be removed soon
        case "randomizeVcIterations":
          ps.GetIntArgument(x => RandomizeVcIterations = x, a => 1 <= a);
          RandomSeed ??= 0; // Set to 0 if not already set
          return true;

        case "vcsLoad":
          double load = 0.0;
          if (ps.GetDoubleArgument(x => load = x))
          {
            if (3.0 <= load)
            {
              ps.Error("surprisingly high load specified; got {0}, expected nothing above 3.0", load.ToString());
              load = 3.0;
            }

            int p = (int) Math.Round(System.Environment.ProcessorCount * load);
            VcsCores = p < 1 ? 1 : p;
          }

          return true;

        case "timeLimit":
          ps.GetUnsignedNumericArgument(x => TimeLimit = x, null);
          return true;

        case "rlimit":
          ps.GetUnsignedNumericArgument(x => ResourceLimit = x);
          return true;

        case "timeLimitPerAssertionInPercent":
          ps.GetUnsignedNumericArgument(x => timeLimitPerAssertionInPercent = x, a => 0 < a);
          return true;

        case "smokeTimeout":
          ps.GetUnsignedNumericArgument(x => SmokeTimeout = x, null);
          return true;

        case "errorLimit":
          ps.GetIntArgument(x => errorLimit = x);
          return true;

        case "randomSeed":
          int randomSeed = 0;
          ps.GetIntArgument(x => randomSeed = x);
          RandomSeed = randomSeed;
          return true;
        
        case "verifySnapshots":
          ps.GetIntArgument(x => VerifySnapshots = x, 4);
          return true;

        case "traceCaching":
          ps.GetIntArgument(x => TraceCaching = x, 4);
          return true;

        case "kInductionDepth":
          ps.GetIntArgument(x => KInductionDepth = x);
          return true;
          
        case "emitDebugInformation":
          ps.GetIntArgument(x => emitDebugInformation = x);
          return true;

        case "normalizeNames":
          ps.GetIntArgument(x => normalizeNames = x);
          return true;
        
        case "normalizeDeclarationOrder":
          ps.GetIntArgument(x => normalizeDeclarationOrder = x);
          return true;

        case "prune":
          ps.GetIntArgument(x => Prune = x);
          return true;

        default:
          bool optionValue = false;
          if (ps.CheckBooleanFlag("printUnstructured", x => optionValue = x))
          {
            PrintUnstructured = optionValue ? 1 : 0;
            return true;
          }

          if (ps.CheckBooleanFlag("printDesugared", x => printDesugarings = x) ||
              ps.CheckBooleanFlag("printLambdaLifting", x => PrintLambdaLifting = x) ||
              ps.CheckBooleanFlag("printInstrumented", x => printInstrumented = x) ||
              ps.CheckBooleanFlag("printPassive", x => UseResolvedProgram.Add(PrintPassiveProgram)) ||
              ps.CheckBooleanFlag("printWithUniqueIds", x => printWithUniqueAstIds = x) ||
              ps.CheckBooleanFlag("wait", x => Wait = x) ||
              ps.CheckBooleanFlag("trace", x => Verbosity = CoreOptions.VerbosityLevel.Trace) ||
              ps.CheckBooleanFlag("quiet", x => Verbosity = CoreOptions.VerbosityLevel.Quiet) ||
              ps.CheckBooleanFlag("silent", x => Verbosity = CoreOptions.VerbosityLevel.Silent) ||
              ps.CheckBooleanFlag("traceTimes", x => TraceTimes = x) ||
              ps.CheckBooleanFlag("tracePOs", x => TraceProofObligations = x) ||
              ps.CheckBooleanFlag("noResolve", x => NoResolve = x) ||
              ps.CheckBooleanFlag("noTypecheck", x => NoTypecheck = x) ||
              ps.CheckBooleanFlag("overlookTypeErrors", x => OverlookBoogieTypeErrors = x) ||
              ps.CheckBooleanFlag("noVerify", x => Verify = x, false) ||
              ps.CheckBooleanFlag("traceverify", x => TraceVerify = x) ||
              ps.CheckBooleanFlag("alwaysAssumeFreeLoopInvariants", x => AlwaysAssumeFreeLoopInvariants = x, true) ||
              ps.CheckBooleanFlag("proverHelp", x => proverHelpRequested = x) ||
              ps.CheckBooleanFlag("proverLogAppend", x => ProverLogFileAppend = x) ||
              ps.CheckBooleanFlag("soundLoopUnrolling", x => SoundLoopUnrolling = x) ||
              ps.CheckBooleanFlag("checkInfer", x => InstrumentWithAsserts = x) ||
              ps.CheckBooleanFlag("restartProver", x => restartProverPerVc = x) ||
              ps.CheckBooleanFlag("printInlined", x => printInlined = x) ||
              ps.CheckBooleanFlag("smoke", x =>
              {
                SoundnessSmokeTest = x;
                Prune = false;
              }) ||
              ps.CheckBooleanFlag("vcsDumpSplits", x => VcsDumpSplits = x) ||
              ps.CheckBooleanFlag("dbgRefuted", x => DebugRefuted = x) ||
              ps.CheckBooleanFlag("reflectAdd", x => ReflectAdd = x) ||
              ps.CheckBooleanFlag("useArrayAxioms", x => useArrayAxioms = x) ||
              ps.CheckBooleanFlag("relaxFocus", x => RelaxFocus = x) ||
              ps.CheckBooleanFlag("doModSetAnalysis", x => doModSetAnalysis = x) ||
              ps.CheckBooleanFlag("runDiagnosticsOnTimeout", x => runDiagnosticsOnTimeout = x) ||
              ps.CheckBooleanFlag("traceDiagnosticsOnTimeout", x => traceDiagnosticsOnTimeout = x) ||
              ps.CheckBooleanFlag("boolControlVC", x => siBoolControlVc = x, true) ||
              ps.CheckBooleanFlag("contractInfer", x => contractInfer = x) ||
              ps.CheckBooleanFlag("explainHoudini", x => explainHoudini = x) ||
              ps.CheckBooleanFlag("reverseHoudiniWorklist", x => reverseHoudiniWorklist = x) ||
              ps.CheckBooleanFlag("crossDependencies", x => houdiniUseCrossDependencies = x) ||
              ps.CheckBooleanFlag("useUnsatCoreForContractInfer", x => useUnsatCoreForContractInfer = x) ||
              ps.CheckBooleanFlag("printAssignment", x => PrintAssignment = x) ||
              ps.CheckBooleanFlag("trackVerificationCoverage", x => trackVerificationCoverage = x) ||
              ps.CheckBooleanFlag("useProverEvaluate", x => useProverEvaluate = x) ||
              ps.CheckBooleanFlag("deterministicExtractLoops", x => DeterministicExtractLoops = x) ||
              ps.CheckBooleanFlag("verifySeparately", x => VerifySeparately = x) ||
              ps.CheckBooleanFlag("trustMoverTypes", x => trustMoverTypes = x) ||
              ps.CheckBooleanFlag("trustNoninterference", x => trustNoninterference = x) ||
              ps.CheckBooleanFlag("trustRefinement", x => trustRefinement = x) ||
              ps.CheckBooleanFlag("trustSequentialization", x => trustSequentialization = x) ||
              ps.CheckBooleanFlag("useBaseNameForFileName", x => UseBaseNameForFileName = x) ||
              ps.CheckBooleanFlag("freeVarLambdaLifting", x => FreeVarLambdaLifting = x) ||
              ps.CheckBooleanFlag("warnNotEliminatedVars", x => WarnNotEliminatedVars = x) ||
              ps.CheckBooleanFlag("keepQuantifier", x => keepQuantifier = x)
          )
          {
            // one of the boolean flags matched
            return true;
          }

          break;
      }

      return base.ParseOption(name, ps); // defer to superclass
    }

    public override void ApplyDefaultOptions()
    {
      Contract.Ensures(TheProverFactory != null);

      base.ApplyDefaultOptions();


      // expand macros in filenames, now that LogPrefix is fully determined
      ExpandFilename(XmlSinkFilename, x => XmlSinkFilename = x, LogPrefix, FileTimestamp);
      ExpandFilename(PrintFile, x => PrintFile = x, LogPrefix, FileTimestamp);
      ExpandFilename(ProverLogFilePath, x => ProverLogFilePath = x, LogPrefix, FileTimestamp);
      ExpandFilename(printErrorModelFile, x => printErrorModelFile = x, LogPrefix, FileTimestamp);

      Contract.Assume(XmlSink == null); // XmlSink is to be set here
      if (XmlSinkFilename != null)
      {
        XmlSink = new XmlSink(this, XmlSinkFilename);
      }

      if (printErrorModelFile != null) {
        ModelWriter = new StreamWriter(printErrorModelFile, false);
      }

      if (TheProverFactory == null)
      {
        ProverDllName = "SMTLib";
        TheProverFactory = ProverFactory.Load(ProverDllName);
      }

      if (StratifiedInlining > 0)
      {
        if (ProverDllName == "SMTLib")
        {
          ErrorLimit = 1;
        }

        if (UseProverEvaluate)
        {
          StratifiedInliningWithoutModels = true;
        }
      }

      if (Trace)
      {
        BoogieDebug.DoPrinting = true; // reuse the -trace option for debug printing
      }
    }

    public override bool ProcessInfoFlags()
    {
      if (base.ProcessInfoFlags())
      {
        return true;
      }

      if (ProverHelpRequested)
      {
        Console.WriteLine(ProverHelp);
        return true;
      }

      return false;
    }


    // Used by Dafny to decide if it should perform compilation
    public bool UserConstrainedProcsToCheck => ProcsToCheck.Count > 0 || ProcsToIgnore.Count > 0;

    public virtual StringCollection ParseNamedArgumentList(string argList)
    {
      if (argList == null || argList.Length == 0)
      {
        return null;
      }

      StringCollection result = new StringCollection();
      int i = 0;
      for (int n = argList.Length; i < n;)
      {
        Cce.LoopInvariant(0 <= i);
        int separatorIndex = this.GetArgumentSeparatorIndex(argList, i);
        if (separatorIndex > i)
        {
          result.Add(argList.Substring(i, separatorIndex - i));
          i = separatorIndex + 1;
          continue;
        }

        result.Add(argList.Substring(i));
        break;
      }

      return result;
    }

    public int GetArgumentSeparatorIndex(string argList, int startIndex)
    {
      Contract.Requires(argList != null);
      Contract.Requires(0 <= startIndex && startIndex <= argList.Length);
      Contract.Ensures(Contract.Result<int>() < argList.Length);
      int commaIndex = argList.IndexOf(",", startIndex);
      int semicolonIndex = argList.IndexOf(";", startIndex);
      if (commaIndex == -1)
      {
        return semicolonIndex;
      }

      if (semicolonIndex == -1)
      {
        return commaIndex;
      }

      if (commaIndex < semicolonIndex)
      {
        return commaIndex;
      }

      return semicolonIndex;
    }

    public string ProverHelp => TheProverFactory.BlankProverOptions(this).Help;

    public override string AttributeHelp =>
@"Boogie: The following attributes are supported by this version.

  ---- On top-level declarations ---------------------------------------------

    {:ignore}
      Ignore the declaration (after checking for duplicate names).

    {:extern}
      If two top-level declarations introduce the same name (for example, two
      constants with the same name or two procedures with the same name), then
      Boogie usually produces an error message.  However, if at least one of
      the declarations is declared with :extern, one of the declarations is
      ignored.  If both declarations are :extern, Boogie arbitrarily chooses
      one of them to keep; otherwise, Boogie ignore the :extern declaration
      and keeps the other.

    {:checksum <string>}
      Attach a checksum to be used for verification result caching.

  ---- On specs -------------------------------------

    {:always_assume}
      On a free requires, it lets the caller assume the pre-condition. Without it,
      the caller simply skips the free requires. On a free ensures,
      it lets the procedure's implementation assume the post-condition.
      Without it, the procedure's implementation ignores the free ensures.
      Boogie ignores this attribute on non-free specs.

  ---- On implementations and procedures -------------------------------------

     {:inline N}
       Inline given procedure (can be also used on implementation).
       N should be a non-negative number and represents the inlining depth.
       With /inline:assume call is replaced with ""assume false"" once inlining depth is reached.
       With /inline:assert call is replaced with ""assert false"" once inlining depth is reached.
       With /inline:spec call is left as is once inlining depth is reached.
       With /inline:none the entire attribute is ignored.
       With /inline:assume and /inline:assert options, methods with the attribute {:inline N} are not verified.

     {:verify false}
       Skip verification of an implementation.

     {:vcs_max_cost N}
     {:vcs_max_splits N}
     {:vcs_max_keep_going_splits N}
     {:vcs_split_on_every_assert}
     {:vcs_split_on_every_assert true}
       Per-implementation versions of
       /vcsMaxCost, /vcsMaxSplits, /vcsMaxKeepGoingSplits and
       /vcsSplitOnEveryAssert.

     {:selective_checking true}
       Turn all asserts into assumes except for the ones reachable from
       assumptions marked with the attribute {:start_checking_here}.
       Thus, ""assume {:start_checking_here} something;"" becomes an inverse
       of ""assume false;"": the first one disables all verification before
       it, and the second one disables all verification after.

     {:priority N}
       Assign a positive priority 'N' to an implementation to control the
       order in which implementations are verified (default: N = 1).

     {:id <string>}
       Assign a unique ID to an implementation to be used for verification
       result caching (default: ""<impl. name>:0""), or assign a unique ID
       to a statement or contract clause for use in identifying which program
       elements were necessary to complete verification. The latter form is
       used by the `/trackVerificationCoverage` option.

     {:timeLimit N}
       Set the time limit for verifying a given implementation.

     {:rlimit N}
       Set the Z3 resource limit for verifying a given implementation.

     {:random_seed N}
       Set the random seed for verifying a given implementation.
       Has the same effect as setting /randomSeed but only for a single implementation.

     {:smt_option name, value}
       Set the SMT option 'name' to 'value', using the SMT-Lib command
       '(set-option :name value)', just for the verification of this
       procedure.

     {:verboseName <string>}
       Set the name to use when printing messages about verification
       status in `/trace` and selecting procedures to verify with
       `/proc`. There are no restrictions on the characters used in the
       string, so it can be particularly useful as a way of describing
       the original name of an identifier translated into Boogie from
       some other source language.

  ---- On axioms -------------------------------------------------------------

    {:include_dep}
      
       Give the axiom an incoming edge from each declaration that it references, which is useful in a migration scenario.
       When turning on pruning in a Boogie program with many axioms,
       one may add {:include_dep} to all of them to prevent pruning too much,
       and then iteratively remove {:include_dep} attributes and add uses clauses to enable pruning more.

  ---- On functions ----------------------------------------------------------

     {:builtin ""spec""}
     {:bvbuiltin ""spec""}
       Rewrite the function to built-in prover function symbol 'fn'.

     {:define}
     {:define true}
       Turn this function into a definition (using the define-fun construct)
       when using the SMT-LIB backend.  Can only be used with non-recursive
       functions. Cannot be combined with :inline attribute.
       Currently works only with monomorphic functions.

     {:inline}
     {:inline true}
       Expand function according to its definition before going to the prover.
       Cannot be combined with :define attribute.

     {:never_pattern true}
       Terms starting with this function symbol will never be
       automatically selected as patterns. It does not prevent them
       from being used inside the triggers, and does not affect explicit
       trigger annotations. Internally it works by adding {:nopats ...}
       annotations to quantifiers.

     {:identity}
     {:identity true}
       If the function has 1 argument and the use of it has type X->X for
       some X, then the abstract interpreter will treat the function as an
       identity function.  Note, the abstract interpreter trusts the
       attribute--it does not try to verify that the function really is an
       identity function.

  ---- On variables ----------------------------------------------------------

     {:existential true}
       Marks a global Boolean variable as existentially quantified. If
       used in combination with option /contractInfer Boogie will check
       whether there exists a Boolean assignment to the existentials
       that makes all verification conditions valid.  Without option
       /contractInfer the attribute is ignored.

  ---- On assert statements --------------------------------------------------

     {:subsumption n}
       Overrides the /subsumption command-line setting for this assertion.

     {:focus}
       Splits verification into two problems. First problem deletes all paths
       that do not have the focus block. Second problem considers the paths
       deleted in the first problem and does not contain either the focus block
       or any block dominated by it.

     {:split_here}
       Verifies code leading to this point and code leading from this point
       to the next split_here as separate pieces.  May help with timeouts.
       May also occasionally double-report errors.

     {:msg <string>}
       Prints <string> rather than the standard message for assertion failure.
       Also applicable to requires and ensures declarations.

  ---- On statements ---------------------------------------------------------

     {:print e0, e1, e2, ...}
       Indicates that expressions e0, e1, e2, ... must be printed.  Must be
       used in conjunction with /enhancedErrorMessages:n command-line option.

     {:captureState s}
       When this attribute is applied to assume commands, it causes the
       /mv:<string> command-line option to group each counterexample model
       into a sequence of states. In particular, this sequence of states
       shows the values of variables at each {:captureState ...} point in
       the counterexample trace. The argument 's' is to be a string, and it
       will be printed as part of /mv's output.

  ---- Pool-based quantifier instantiation -----------------------------------

     {:pool ""name""}
       Used on a bound variable of a quantifier or lambda. Indicates that
       expressions in pool name should be used for instantiating that variable.

     {:add_to_pool ""name"", e}
       Used on an assert or assume command. Adds the expression e to pool name
       after substituting variables with their incarnations at the command.

       Used on a quantifier. Adds the expression e, after substituting the
       bound variables with fresh skolem constants, whenever the quantifier is
       skolemized.

     These attributes are not effective for quantifiers inside the scope of axioms.

  ---- Civl ------------------------------------------------------------------

     {:yields}
       Yielding loop.

     {:layer N}
     {:layer M, N}
     {:layer N1, N2, ...}
       Layer number, layer range, or set of layer numbers, respectively.

     {:hide}
       Hidden input/output parameter.

     {:pending_async}
       Local variable collecting pending asyncs in yielding procedure.

     {:sync}
       Synchronized async call.

     {:linear ""domain""}
       Permission type for domain.
       Collector function for domain.
       Linear variable (both global and local).

     {:linear_in ""domain""}
     {:linear_out ""domain""}
       Linear input/output parameter.";

    protected override string HelpHeader =>
      base.HelpHeader + @"
  /env:<n>      print command line arguments
                  0 - never, 1 (default) - during BPL print and prover log,
                  2 - like 1 and also to standard output
  /printVerifiedProceduresCount:<n>
                0 - no
                1 (default) - yes
  /wait         await Enter from keyboard before terminating program
  /xml:<file>   also produce output in XML format to <file>
";

    protected override string HelpBody =>
      @"
  ---- Boogie options --------------------------------------------------------

  Multiple .bpl files supplied on the command line are concatenated into one
  Boogie program.

  /lib:<name>    : Include definitions in library <name>. The file <name>.bpl
                   must be an included resource in Core.dll. Currently, the
                   following libraries are supported---base, node.
  /proc:<p>      : Only check procedures matched by pattern <p>. This option
                   may be specified multiple times to match multiple patterns.
                   The pattern <p> matches the whole procedure name and may
                   contain * wildcards which match any character zero or more
                   times.
  /noProc:<p>    : Do not check procedures matched by pattern <p>. Exclusions
                   with /noProc are applied after inclusions with /proc.
  /noResolve     : parse only
  /noTypecheck   : parse and resolve only

  /print:<file>  : print Boogie program after parsing it
                   (use - as <file> to print to console)
  /pretty:<n>
                0 - print each Boogie statement on one line (faster).
                1 (default) - pretty-print with some line breaks.
  /printWithUniqueIds : print augmented information that uniquely
                   identifies variables
  /printUnstructured : with /print option, desugars all structured statements
  /printPassive :  with /print option, prints passive version of program
  /printDesugared : with /print option, desugars calls
  /printLambdaLifting : with /print option, desugars lambda lifting

  /freeVarLambdaLifting : Boogie's lambda lifting transforms the bodies of lambda
                         expressions into templates with holes. By default, holes
                         are maximally large subexpressions that do not contain
                         bound variables. This option performs a form of lambda
                         lifting in which holes are the lambda's free variables.

  /overlookTypeErrors : skip any implementation with resolution or type
                        checking errors

  /loopUnroll:<n>
                unroll loops, following up to n back edges (and then some)
  /soundLoopUnrolling
                sound loop unrolling
  /doModSetAnalysis
                automatically infer modifies clauses
  /printModel:<n>
                0 (default) - do not print Z3's error model
                1 - print Z3's error model
  /printModelToFile:<file>
                print model to <file> instead of console
  /mv:<file>    Specify file to save the model with captured states
                (see documentation for :captureState attribute)
  /enhancedErrorMessages:<n>
                0 (default) - no enhanced error messages
                1 - Z3 error model enhanced error messages

  /printCFG:<prefix> : print control flow graph of each implementation in
                       Graphviz format to files named:
                         <prefix>.<procedure name>.dot

  /useBaseNameForFileName : When parsing use basename of file for tokens instead
                            of the path supplied on the command line

  /emitDebugInformation:<n>
                0 - do not emit debug information
                1 (default) - emit the debug information :qid, :skolemid and set-info :boogie-vc-id

  /normalizeNames:<n>
                0 (default) - Keep Boogie program names when generating SMT commands
                1 - Normalize Boogie program names when generating SMT commands. 
                  This keeps SMT solver input, and thus output, 
                  constant when renaming declarations in the input program.

  /normalizeDeclarationOrder:<n>
                0 - Keep order of top-level declarations when generating SMT commands.
                1 (default) - Normalize order of top-level declarations when generating SMT commands.
                  This keeps SMT solver input, and thus output, 
                  constant when reordering declarations in the input program.

  ---- Inference options -----------------------------------------------------

  /infer:<flags>
                use abstract interpretation to infer invariants
                <flags> must specify exactly one of the following domains:
                   t = trivial bottom/top lattice
                   j = stronger intervals
                together with any of the following options:
                   s = debug statistics
                0..9 = number of iterations before applying a widen (default=0)
  /checkInfer   instrument inferred invariants as asserts to be checked by
                theorem prover
  /contractInfer
                perform procedure contract inference
  /instrumentInfer
                h - instrument inferred invariants only at beginning of
                    loop headers (default)
                e - instrument inferred invariants at beginning and end
                    of every block (this mode is intended for use in
                    debugging of abstract domains)
  /printInstrumented
                print Boogie program after it has been instrumented with
                invariants

  ---- Debugging and general tracing options ---------------------------------

  /silent       print nothing at all
  /quiet        print nothing but warnings and errors
  /trace        blurt out various debug trace information
  /traceTimes   output timing information at certain points in the pipeline
  /tracePOs     output information about the number of proof obligations
                (also included in the /trace output)
  /break        launch and break into debugger

  ---- Civl options ----------------------------------------------------------

  /trustMoverTypes
                do not verify mover type annotations on atomic action declarations
  /trustNoninterference
                do not perform noninterference checks
  /trustRefinement
                do not perform refinement checks
  /trustLayersUpto:<n>
                do not verify layers <n> and below
  /trustLayersDownto:<n>
                do not verify layers <n> and above
  /trustSequentialization
                do not perform sequentialization checks
  /civlDesugaredFile:<file>
                print plain Boogie program to <file>

  ---- Verification-condition generation options -----------------------------

  /liveVariableAnalysis:<c>
                0 = do not perform live variable analysis
                1 = perform live variable analysis (default)
                2 = perform interprocedural live variable analysis
  /noVerify     skip VC generation and invocation of the theorem prover
  /verifySnapshots:<n>
                verify several program snapshots (named <filename>.v0.bpl
                to <filename>.vN.bpl) using verification result caching:
                0 - do not use any verification result caching (default)
                1 - use the basic verification result caching
                2 - use the more advanced verification result caching
                3 - use the more advanced caching and report errors according
                    to the new source locations for errors and their
                    related locations (but not /errorTrace and CaptureState
                    locations)
  /traceCaching:<n>
                0 (default) - none
                1 - for testing
                2 - for benchmarking
                3 - for testing, benchmarking, and debugging
  /verifySeparately
                verify each input program separately
  /removeEmptyBlocks:<c>
                0 - do not remove empty blocks during VC generation
                1 - remove empty blocks (default)
  /coalesceBlocks:<c>
                0 = do not coalesce blocks
                1 = coalesce blocks (default)
  /traceverify  print debug output during verification condition generation
  /subsumption:<c>
                apply subsumption to asserted conditions:
                0 - never, 1 - not for quantifiers, 2 (default) - always
  /alwaysAssumeFreeLoopInvariants
                usually, a free loop invariant (or assume
                statement in that position) is ignored in checking contexts
                (like other free things); this option includes these free
                loop invariants as assumes in both contexts
  /inline:<i>   use inlining strategy <i> for procedures with the :inline
                attribute, see /attrHelp for details:
                  none
                  assume (default)
                  assert
                  spec
  /printInlined
                print the implementation after inlining calls to
                procedures with the :inline attribute (works with /inline)
  /recursionBound:<n>
                Set the recursion bound for stratified inlining to
                be n (default 500)
  /smoke        Soundness Smoke Test: try to stick assert false; in some
                places in the BPL and see if we can still prove it
  /smokeTimeout:<n>
                Timeout, in seconds, for a single theorem prover
                invocation during smoke test, defaults to 10.
  /typeEncoding:<t>
                Encoding of types when generating VC of a polymorphic program:
                   m = monomorphic (default)
                   p = predicates
                   a = arguments
                Boogie automatically detects monomorphic programs and enables
                monomorphic VC generation, thereby overriding the above option.
                If the latter two options are used, then arrays are handled via axioms.
  /useArrayAxioms
                If monomorphic type encoding is used, arrays are handled by default with
                the SMT theory of arrays. This option allows the use of axioms instead.
  /reflectAdd   In the VC, generate an auxiliary symbol, elsewhere defined
                to be +, instead of +.
  /prune:<n>
                0 - Turn off pruning.
                1 - Turn on pruning (default). Pruning will remove any top-level
                Boogie declarations that are not accessible by the implementation
                that is about to be verified. Without pruning, due to the unstable
                nature of SMT solvers, a change to any part of a Boogie program
                has the potential to affect the verification of any other part of
                the program.

                Only use this if your program contains uses clauses
                where required, otherwise pruning will break your program.
                More information can be found here: https://github.com/boogie-org/boogie/blob/afe8eb0ffbb48d593de1ae3bf89712246444daa8/Source/ExecutionEngine/CommandLineOptions.cs#L160
  /printPruned:<file>
                After pruning, print the Boogie program to the specified file.
  /relaxFocus   Process foci in a bottom-up fashion. This way only generates
                a linear number of splits. The default way (top-down) is more
                aggressive and it may create an exponential number of splits.
  /randomSeed:<s>
                Supply the random seed for /randomizeVcIterations option.
  /randomizeVcIterations:<n>
                Turn on randomization of the input that Boogie passes to the
                SMT solver and turn on randomization in the SMT solver itself.
                Attempt to randomize and prove each VC n times using the random
                seed s provided by the option /randomSeed:<s>. If /randomSeed option
                is not provided, s is chosen to be zero.

                Certain Boogie inputs are unstable in the sense that changes to 
                the input that preserve its meaning may cause the output to change.
                This option simulates meaning-preserving changes to the input
                without requiring the user to actually make those changes.
                This option is implemented by renaming variables and reordering
                declarations in the input, and by setting solver options that have
                similar effects.
  /trackVerificationCoverage
                Track and report which program elements labeled with an
                `{:id ...}` attribute were necessary to complete verification.
                Assumptions, assertions, requires clauses, ensures clauses,
                assignments, and calls can be labeled for inclusion in this
                report. This generalizes and replaces the previous
                (undocumented) `/printNecessaryAssertions` option.

  /keepQuantifier
                If pool-based quantifier instantiation creates instances of a quantifier
                then keep the quantifier along with the instances. By default, the quantifier
                is dropped if any instances are created.

  ---- Verification-condition splitting --------------------------------------

  /vcsMaxCost:<f>
                VC will not be split unless the cost of a VC exceeds this
                number, defaults to 2000.0. This does NOT apply in the
                keep-going mode after first round of splitting.
  /vcsMaxSplits:<n>
                Maximal number of VC generated per method. In keep
                going mode only applies to the first round.
                Defaults to 1.
  /vcsMaxKeepGoingSplits:<n>
                If set to more than 1, activates the keep
                going mode, where after the first round of splitting,
                VCs that timed out are split into <n> pieces and retried
                until we succeed proving them, or there is only one
                assertion on a single path and it timeouts (in which
                case error is reported for that assertion).
                Defaults to 1.
  /vcsKeepGoingTimeout:<n>
                Timeout in seconds for a single theorem prover
                invocation in keep going mode, except for the final
                single-assertion case. Defaults to 1s.
  /vcsFinalAssertTimeout:<n>
                Timeout in seconds for the single last
                assertion in the keep going mode. Defaults to 30s.
  /vcsPathJoinMult:<f>
                If more than one path join at a block, by how much
                multiply the number of paths in that block, to accomodate
                for the fact that the prover will learn something on one
                paths, before proceeding to another. Defaults to 0.8.
  /vcsPathCostMult:<f1>
  /vcsAssumeMult:<f2>
                The cost of a block is
                    (<assert-cost> + <f2>*<assume-cost>) *
                    (1.0 + <f1>*<entering-paths>)
                <f1> defaults to 1.0, <f2> defaults to 0.01.
                The cost of a single assertion or assumption is
                currently always 1.0.
  /vcsPathSplitMult:<f>
                If the best path split of a VC of cost A is into
                VCs of cost B and C, then the split is applied if
                A >= <f>*(B+C), otherwise assertion splitting will be
                applied. Defaults to 0.5 (always do path splitting if
                possible), set to more to do less path splitting
                and more assertion splitting.
  /vcsSplitOnEveryAssert
                Splits every VC so that each assertion is isolated
                into its own VC. May result in VCs without any assertions.
  /vcsDumpSplits
                For split #n dump split.n.dot and split.n.bpl.
                Warning: Affects error reporting.
  /vcsCores:<n>
                Try to verify <n> VCs at once. Defaults to 1.
  /vcsLoad:<f>  Sets vcsCores to the machine's ProcessorCount * f,
                rounded to the nearest integer (where 0.0 <= f <= 3.0),
                but never to less than 1.

  ---- Prover options --------------------------------------------------------

  /errorLimit:<num>
                Limit the number of errors produced for each procedure
                (default is 5, some provers may support only 1).
                Set num to 0 to find as many assertion failures as possible.
  /timeLimit:<num>
                Limit the number of seconds spent trying to verify
                each procedure
  /rlimit:<num>
                Limit the Z3 resource spent trying to verify each procedure.
  /errorTrace:<n>
                0 - no Trace labels in the error output,
                1 (default) - include useful Trace labels in error output,
                2 - include all Trace labels in the error output
  /vcBrackets:<b>
                bracket odd-charactered identifier names with |'s.  <b> is:
                   0 - no (default),
                   1 - yes
  /proverDll:<tp>
                use theorem prover <tp>, where <tp> is either the name of
                a DLL containing the prover interface located in the
                Boogie directory, or a full path to a DLL containing such
                an interface. The default interface shipped is:
                    SMTLib (uses the SMTLib2 format and calls an SMT solver)
  /proverOpt:KEY[=VALUE]
                Provide a prover-specific option (short form /p).
  /proverHelp   Print prover-specific options supported by /proverOpt.
  /proverLog:<file>
                Log input for the theorem prover.  Like filenames
                supplied as arguments to other options, <file> can use the
                following macros:
                    @TIME@    expands to the current time
                    @PREFIX@  expands to the concatenation of strings given
                              by /logPrefix options
                    @FILE@    expands to the last filename specified on the
                              command line
                In addition, /proverLog can also use the macro '@PROC@',
                which causes there to be one prover log file per
                verification condition, and the macro then expands to the
                name of the procedure that the verification condition is for.
  /logPrefix:<str>
                Defines the expansion of the macro '@PREFIX@', which can
                be used in various filenames specified by other options.
  /proverLogAppend
                Append (not overwrite) the specified prover log file
  /proverWarnings
                0 (default) - don't print, 1 - print to stdout,
                2 - print to stderr
  /restartProver
                Restart the prover after each query";
  }
}
