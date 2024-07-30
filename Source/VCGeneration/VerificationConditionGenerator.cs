using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using System.IO;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.BaseTypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{

  using Bpl = Microsoft.Boogie;
  using System.Threading.Tasks;


  record ImplementationTransformationData
  {

    public bool Passified { get; set; } = false;
    public bool ConvertedToDAG { get; set; } = false;
    public Dictionary<TransferCmd, ReturnCmd> GotoCmdOrigins { get; set; }
    public ModelViewInfo ModelViewInfo { get; set; }
  }


  public class VerificationConditionGenerator : ConditionGeneration
  {
    private static ConditionalWeakTable<Implementation, ImplementationTransformationData> implementationData = new();


    /// <summary>
    /// Constructor.  Initializes the theorem prover.
    /// </summary>
    [NotDelayed]
    public VerificationConditionGenerator(Program program, CheckerPool checkerPool)
      : base(program, checkerPool)
    {
      Contract.Requires(program != null);
    }

    public static AssumeCmd AssertTurnedIntoAssume(VCGenOptions options, AssertCmd assrt)
    {
      Contract.Requires(assrt != null);
      Contract.Ensures(Contract.Result<AssumeCmd>() != null);

      Expr expr = assrt.Expr;
      Contract.Assert(expr != null);
      switch (Wlp.Subsumption(options, assrt))
      {
        case CoreOptions.SubsumptionOption.Never:
          expr = Expr.True;
          break;
        case CoreOptions.SubsumptionOption.Always:
          break;
        case CoreOptions.SubsumptionOption.NotForQuantifiers:
          if (expr is QuantifierExpr)
          {
            expr = Expr.True;
          }

          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected case
      }

      var assume = new AssumeCmd(assrt.tok, expr);
      if (expr != Expr.True)
      {
        // Copy any {:id ...} from the assertion to the assumption, so
        // we can track it while analyzing verification coverage. But
        // skip it if it's `true` because that's never useful to track.
        (assume as ICarriesAttributes).CopyIdFrom(assrt.tok, assrt);
      }

      return assume;
    }

    #region Soundness smoke tester

    #endregion

    public class CodeExprConversionClosure
    {
      private readonly TextWriter traceWriter;
      private readonly VCGenOptions options;
      ControlFlowIdMap<Absy> absyIds;
      ProverContext ctx;

      public CodeExprConversionClosure(TextWriter traceWriter, VCGenOptions options, ControlFlowIdMap<Absy> absyIds,
        ProverContext ctx)
      {
        this.traceWriter = traceWriter;
        this.options = options;
        this.absyIds = absyIds;
        this.ctx = ctx;
      }

      public VCExpr CodeExprToVerificationCondition(CodeExpr codeExpr, List<VCExprLetBinding> bindings,
        bool isPositiveContext, Dictionary<Cmd, List<object>> debugInfos)
      {
        VerificationConditionGenerator vcgen =
          new VerificationConditionGenerator(new Program(), new CheckerPool(options));
        vcgen.variable2SequenceNumber = new Dictionary<Variable, int>();
        vcgen.incarnationOriginMap = new Dictionary<Incarnation, Absy>();
        vcgen.CurrentLocalVariables = codeExpr.LocVars;

        ResetPredecessors(codeExpr.Blocks);
        vcgen.AddBlocksBetween(codeExpr.Blocks);
        Dictionary<Variable, Expr> gotoCmdOrigins = vcgen.ConvertBlocks2PassiveCmd(traceWriter, codeExpr.Blocks,
          new List<IdentifierExpr>(), new ModelViewInfo(codeExpr), debugInfos);
        VCExpr startCorrect = vcgen.LetVC(codeExpr.Blocks, null, absyIds, ctx, out var ac, isPositiveContext);
        VCExpr vce = ctx.ExprGen.Let(bindings, startCorrect);
        if (vcgen.CurrentLocalVariables.Count != 0)
        {
          Boogie2VCExprTranslator translator = ctx.BoogieExprTranslator;
          List<VCExprVar> boundVars = new List<VCExprVar>();
          foreach (Variable v in vcgen.CurrentLocalVariables)
          {
            Contract.Assert(v != null);
            VCExprVar ev = translator.LookupVariable(v);
            Contract.Assert(ev != null);
            boundVars.Add(ev);
            if (v.TypedIdent.Type.Equals(Bpl.Type.Bool))
            {
              // add an antecedent (tickleBool ev) to help the prover find a possible trigger
              vce = ctx.ExprGen.Implies(ctx.ExprGen.Function(VCExpressionGenerator.TickleBoolOp, ev), vce);
            }
          }

          vce = ctx.ExprGen.Forall(boundVars, new List<VCTrigger>(), vce);
        }

        if (isPositiveContext)
        {
          vce = ctx.ExprGen.Not(vce);
        }

        return vce;
      }
    }

    public VCExpr GenerateVC(Implementation /*!*/ impl, VCExpr controlFlowVariableExpr,
      ControlFlowIdMap<Absy> absyIds, ProverContext proverContext)
    {
      Contract.Requires(impl != null);
      Contract.Requires(proverContext != null);
      Contract.Ensures(Contract.ValueAtReturn(out absyIds) != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      return GenerateVCAux(impl, controlFlowVariableExpr, absyIds, proverContext);
    }

    public VCExpr GenerateVCAux(Implementation /*!*/ impl, VCExpr controlFlowVariableExpr,
      ControlFlowIdMap<Absy> /*!*/ absyIds, ProverContext proverContext)
    {
      Contract.Requires(impl != null);
      Contract.Requires(proverContext != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      TypecheckingContext tc = new TypecheckingContext(null, Options);
      impl.Typecheck(tc);

      VCExpr vc;
      int assertionCount;
      if (cce.NonNull(CheckerPool.Options.TheProverFactory).SupportsDags)
      {
        vc = DagVC(cce.NonNull(impl.Blocks[0]), controlFlowVariableExpr, absyIds,
          new Dictionary<Block, VCExpr>(), proverContext, out assertionCount);
      }
      else
      {
        vc = LetVC(impl.Blocks, controlFlowVariableExpr, absyIds, proverContext, out assertionCount);
      }

      CumulativeAssertionCount += assertionCount;
      if (assertionCount == 0)
      {
        return VCExpressionGenerator.True;
      }

      return vc;
    }

    public static void CheckIntAttributeOnImpl(ImplementationRun run, string name, ref int val)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      Contract.Requires(name != null);
      if (impl.FindAttribute(name) == null || impl.CheckIntAttribute(name, ref val))
      {
        return;
      }

      run.OutputWriter.WriteLine("ignoring ill-formed {:{0} ...} attribute on {1}, parameter should be an int", name,
        impl.Name);
    }

    // If "expand" attribute is supplied, expand any assertion of conjunctions into multiple assertions, one per conjunct
    void ExpandAsserts(Implementation impl)
    {
      foreach (var b in impl.Blocks)
      {
        List<Cmd> newCmds = new List<Cmd>();
        bool changed = false;
        foreach (var c in b.Cmds)
        {
          var a = c as AssertCmd;
          var ar = c as AssertRequiresCmd;
          var ae = c as AssertEnsuresCmd;
          var ai = c as LoopInitAssertCmd;
          var am = c as LoopInvMaintainedAssertCmd;
          // TODO:
          //use Duplicator and Substituter rather than new
          //nested IToken?
          //document expand attribute (search for {:ignore}, for example)
          //fix up new CallCmd, new Requires, new Ensures in CivlRefinement.cs
          Func<Expr, Expr, Expr> withType = (Expr from, Expr to) =>
          {
            NAryExpr nFrom = from as NAryExpr;
            NAryExpr nTo = to as NAryExpr;
            to.Type = from.Type;
            if (nFrom != null && nTo != null)
            {
              nTo.TypeParameters = nFrom.TypeParameters;
            }

            return to;
          };

          Action<int, Expr, Action<Expr>> traverse = null;
          traverse = (depth, e, act) =>
          {
            ForallExpr forall = e as ForallExpr;
            NAryExpr nary = e as NAryExpr;
            if (forall != null)
            {
              traverse(depth, forall.Body, e1 => act(withType(forall,
                new ForallExpr(e1.tok, forall.TypeParameters, forall.Dummies, forall.Attributes, forall.Triggers,
                  e1))));
              return;
            }

            if (nary != null)
            {
              var args = nary.Args;
              IAppliable fun = nary.Fun;
              BinaryOperator bop = fun as BinaryOperator;
              FunctionCall call = fun as FunctionCall;
              if (bop != null)
              {
                switch (bop.Op)
                {
                  case BinaryOperator.Opcode.And:
                    traverse(depth, args[0], act);
                    traverse(depth, args[1], act);
                    return;
                  case BinaryOperator.Opcode.Imp:
                    traverse(depth, args[1], e1 => act(withType(nary,
                      new NAryExpr(e1.tok, fun, new List<Expr>() { args[0], e1 }))));
                    return;
                }
              }

              if (depth > 0 && call != null && call.Func != null)
              {
                Function cf = call.Func;
                Expr body = cf.Body;
                List<Variable> ins = cf.InParams;
                if (body == null && cf.DefinitionAxiom != null)
                {
                  ForallExpr all = cf.DefinitionAxiom.Expr as ForallExpr;
                  if (all != null)
                  {
                    NAryExpr def = all.Body as NAryExpr;
                    if (def != null && def.Fun is BinaryOperator &&
                        ((BinaryOperator)(def.Fun)).Op == BinaryOperator.Opcode.Iff)
                    {
                      body = def.Args[1];
                      ins = all.Dummies;
                    }
                  }
                }

                if (body != null)
                {
                  Func<Expr, Expr> new_f = e1 =>
                  {
                    Function f = new Function(cf.tok, "expand<" + cf.Name + ">", cf.TypeParameters, ins,
                      cf.OutParams[0], cf.Comment);
                    f.Body = e1;
                    Token tok = new Token(e1.tok.line, e1.tok.col);
                    tok.filename = e.tok.filename + "(" + e.tok.line + "," + e.tok.col + ") --> " + e1.tok.filename;
                    return withType(nary, new NAryExpr(tok, new FunctionCall(f), args));
                  };
                  traverse(depth - 1, body, e1 => act(new_f(e1)));
                  return;
                }
              }
            }

            act(e);
          };

          if (a != null)
          {
            var attr = a.Attributes;
            if (ar != null && ar.Requires.Attributes != null)
            {
              attr = ar.Requires.Attributes;
            }

            if (ar != null && ar.Call.Attributes != null)
            {
              attr = ar.Call.Attributes;
            }

            if (ae != null && ae.Ensures.Attributes != null)
            {
              attr = ae.Ensures.Attributes;
            }

            if (QKeyValue.FindExprAttribute(attr, "expand") != null || QKeyValue.FindBoolAttribute(attr, "expand"))
            {
              int depth = QKeyValue.FindIntAttribute(attr, "expand", 100);
              Func<Expr, Expr> fe = e => Expr.Or(a.Expr, e);
              //traverse(depth, a.Expr, e => System.Console.WriteLine(e.GetType() + " :: " + e + " @ " + e.tok.line + ", " + e.tok.col));
              traverse(depth, a.Expr, e =>
              {
                AssertCmd new_c =
                  (ar != null) ? new AssertRequiresCmd(ar.Call,
                    new Requires(e.tok, ar.Requires.Free, fe(e), ar.Requires.Comment)) :
                  (ae != null) ? new AssertEnsuresCmd(new Ensures(e.tok, ae.Ensures.Free, fe(e), ae.Ensures.Comment)) :
                  (ai != null) ? new LoopInitAssertCmd(e.tok, fe(e), ai.originalAssert) :
                  (am != null) ? new LoopInvMaintainedAssertCmd(e.tok, fe(e), am.originalAssert) :
                  new AssertCmd(e.tok, fe(e));
                new_c.Description = a.Description;
                new_c.Attributes = new QKeyValue(e.tok, "subsumption",
                  new List<object>() { new LiteralExpr(e.tok, BigNum.FromInt(0)) }, a.Attributes);
                newCmds.Add(new_c);
              });
            }

            newCmds.Add(c);
            changed = true;
          }
          else
          {
            newCmds.Add(c);
          }
        }

        if (changed)
        {
          b.Cmds = newCmds;
        }
      }
    }

    public VCGenOptions Options => CheckerPool.Options;

    public override async Task<VcOutcome> VerifyImplementation(ImplementationRun run, VerifierCallback callback,
      CancellationToken cancellationToken)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var impl = run.Implementation;

      if (run.Implementation.IsSkipVerification(Options))
      {
        return VcOutcome.Inconclusive; // not sure about this one
      }

      callback.OnProgress?.Invoke("VCgen", 0, 0, 0.0);

      PrepareImplementation(run, callback, out var smokeTester, out var dataGotoCmdOrigins, out var dataModelViewInfo);

      VcOutcome vcOutcome = VcOutcome.Correct;

      // Report all recycled failing assertions for this implementation.
      if (impl.RecycledFailingAssertions != null && impl.RecycledFailingAssertions.Any())
      {
        vcOutcome = VcOutcome.Errors;
        foreach (var a in impl.RecycledFailingAssertions)
        {
          var checksum = a.Checksum;
          if (impl.ErrorChecksumToCachedError[checksum] is Counterexample oldCex)
          {
            if (Options.VerifySnapshots < 3)
            {
              callback.OnCounterexample(oldCex, null);
            }
            else
            {
              // If possible, we use the old counterexample, but with the location information of "a"
              var cex = AssertCmdToCloneCounterexample(CheckerPool.Options, a, oldCex, impl.Blocks[0],
                dataGotoCmdOrigins);
              callback.OnCounterexample(cex, null);
            }
          }
        }
      }

      var worker = new SplitAndVerifyWorker(Options, this, run, dataGotoCmdOrigins, callback,
        dataModelViewInfo, vcOutcome);

      vcOutcome = await worker.WorkUntilDone(cancellationToken);
      ResourceCount = worker.ResourceCount;

      TotalProverElapsedTime = worker.TotalProverElapsedTime;
      if (vcOutcome == VcOutcome.Correct && smokeTester != null)
      {
        await smokeTester.Test(run.OutputWriter);
      }

      callback.OnProgress?.Invoke("done", 0, 0, 1.0);

      return vcOutcome;
    }

    public void PrepareImplementation(ImplementationRun run, VerifierCallback callback,
      out SmokeTester smokeTester,
      out Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins,
      out ModelViewInfo modelViewInfo)
    {
      var data = implementationData.GetOrCreateValue(run.Implementation)!;
      if (!data.ConvertedToDAG)
      {
        data.ConvertedToDAG = true;
        ConvertCFG2DAG(run);
      }

      smokeTester = null;
      if (Options.SoundnessSmokeTest)
      {
        smokeTester = new SmokeTester(this, run, callback);
        smokeTester.Copy();
      }

      if (!data.Passified)
      {
        data.Passified = true;
        data.GotoCmdOrigins = gotoCmdOrigins = PassifyImpl(run, out modelViewInfo);
        data.ModelViewInfo = modelViewInfo;

        ExpandAsserts(run.Implementation);
        
        if (Options.PrintPassiveFile != null) {
          lock (Options) {
            var prev = Options.PrintUnstructured;
            Options.PrintUnstructured = 2;
            using var writer = new TokenTextWriter(Options.PrintPassiveFile, false, false, Options);
            writer.WriteLine();
            program.Emit(writer);
            Options.PrintUnstructured = prev;
          }
        }
      }
      else
      {
        modelViewInfo = data.ModelViewInfo;
        gotoCmdOrigins = data.GotoCmdOrigins;
      }

    }

    public class ErrorReporter : ProverInterface.ErrorHandler
    {
      private ProofRun split;
      private new VCGenOptions options;
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins;

      ControlFlowIdMap<Absy> absyIds;

      List<Block> blocks;

      protected Dictionary<Cmd, List<object>> debugInfos;

      protected VerifierCallback callback;

      protected ModelViewInfo MvInfo;
      public string resourceExceededMessage;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(gotoCmdOrigins != null);
        Contract.Invariant(absyIds != null);
        Contract.Invariant(cce.NonNullElements(blocks));
        Contract.Invariant(callback != null);
        Contract.Invariant(context != null);
        Contract.Invariant(program != null);
      }

      protected ProverContext context;

      Program program;

      public override void AddCoveredElement(TrackedNodeComponent elt)
      {
        program.AllCoveredElements.Push(elt);
        split.CoveredElements.Add(elt);
      }

      public ErrorReporter(VCGenOptions options,
        Dictionary<TransferCmd, ReturnCmd> /*!*/ gotoCmdOrigins,
        ControlFlowIdMap<Absy> /*!*/ absyIds,
        List<Block /*!*/> /*!*/ blocks,
        Dictionary<Cmd, List<object>> debugInfos,
        VerifierCallback /*!*/ callback,
        ModelViewInfo mvInfo,
        ProverContext /*!*/ context,
        Program /*!*/ program, ProofRun split) : base(options)
      {
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(absyIds != null);
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(callback != null);
        Contract.Requires(context != null);
        Contract.Requires(program != null);
        this.gotoCmdOrigins = gotoCmdOrigins;
        this.absyIds = absyIds;
        this.blocks = blocks;
        this.debugInfos = debugInfos;
        this.callback = callback;
        this.MvInfo = mvInfo;

        this.context = context;
        this.program = program;
        this.split = split;
        this.options = options;
      }

      public override void OnModel(IList<string> labels /*!*/ /*!*/, Model model,
        SolverOutcome proverOutcome)
      {
        // no counter examples reported.
        if (labels.Count == 0)
        {
          return;
        }

        var traceNodes = new HashSet<Absy>();
        foreach (string s in labels)
        {
          Contract.Assert(s != null);
          Absy absy = Label2Absy(s);
          Contract.Assert(absy != null);
          if (traceNodes.Contains(absy))
          {
            options.OutputWriter.WriteLine("Warning: duplicate label: " + s + " read while tracing nodes");
          }
          else
          {
            traceNodes.Add(absy);
          }
        }

        List<Block> trace = new List<Block>();
        Block entryBlock = cce.NonNull(this.blocks[0]);
        Contract.Assert(traceNodes.Contains(entryBlock));
        trace.Add(entryBlock);

        Counterexample newCounterexample = TraceCounterexample(options, entryBlock, traceNodes, trace, model, MvInfo,
          debugInfos, context, split, new Dictionary<TraceLocation, CalleeCounterexampleInfo>());

        if (newCounterexample == null)
        {
          return;
        }

        #region Map passive program errors back to original program errors

        ReturnCounterexample returnExample = newCounterexample as ReturnCounterexample;
        if (returnExample != null)
        {
          foreach (Block b in returnExample.Trace)
          {
            Contract.Assert(b != null);
            Contract.Assume(b.TransferCmd != null);
            ReturnCmd cmd = gotoCmdOrigins.ContainsKey(b.TransferCmd) ? gotoCmdOrigins[b.TransferCmd] : null;
            if (cmd != null)
            {
              returnExample.FailingReturn = cmd;
              break;
            }
          }
        }

        #endregion

        callback.OnCounterexample(newCounterexample, null);
        split.Counterexamples.Add(newCounterexample);
      }

      public override Absy Label2Absy(string label)
      {
        //Contract.Requires(label != null);
        Contract.Ensures(Contract.Result<Absy>() != null);

        int id = int.Parse(label);
        return cce.NonNull(absyIds.GetValue(id));
      }

      public override void OnResourceExceeded(string msg, IEnumerable<Tuple<AssertCmd, TransferCmd>> assertCmds = null)
      {
        //Contract.Requires(msg != null);
        resourceExceededMessage = msg;
        if (assertCmds != null)
        {
          foreach (var cmd in assertCmds)
          {
            Counterexample cex =
              AssertCmdToCounterexample(options, cmd.Item1, cmd.Item2, new List<Block>(),
                new List<object>(), null, null, context, null);
            cex.IsAuxiliaryCexForDiagnosingTimeouts = true;
            callback.OnCounterexample(cex, msg);
          }
        }
      }

      public override void OnProverWarning(string msg)
      {
        //Contract.Requires(msg != null);
        callback.OnWarning(options, msg);
      }
    }

    private void RecordCutEdge(Dictionary<Block, List<Block>> edgesCut, Block from, Block to)
    {
      if (edgesCut != null)
      {
        if (!edgesCut.ContainsKey(from))
        {
          edgesCut.Add(from, new List<Block>());
        }

        edgesCut[from].Add(to);
      }
    }

    public void ConvertCFG2DAG(ImplementationRun run, Dictionary<Block, List<Block>> edgesCut = null, int taskID = -1)
    {
      var impl = run.Implementation;
      Contract.Requires(impl != null);
      impl.PruneUnreachableBlocks(
        Options); // This is needed for VCVariety.BlockNested, and is otherwise just an optimization

      CurrentLocalVariables = impl.LocVars;
      variable2SequenceNumber = new Dictionary<Variable, int>();
      incarnationOriginMap = new Dictionary<Incarnation, Absy>();

      #region Debug Tracing

      if (Options.TraceVerify)
      {
        run.OutputWriter.WriteLine("original implementation");
        EmitImpl(Options, run, false);
      }

      #endregion

      #region Debug Tracing

      if (Options.TraceVerify)
      {
        run.OutputWriter.WriteLine("after desugaring sugared commands like procedure calls");
        EmitImpl(Options, run, true);
      }

      #endregion

      // Recompute the predecessors, but first insert a dummy start node that is sure not to be the target of any goto (because the cutting of back edges
      // below assumes that the start node has no predecessor)
      impl.Blocks.Insert(0,
        new Block(new Token(-17, -4), "0", new List<Cmd>(),
          new GotoCmd(Token.NoToken, new List<String> { impl.Blocks[0].Label }, new List<Block> { impl.Blocks[0] })));
      ResetPredecessors(impl.Blocks);

      var k = Math.Max(Options.KInductionDepth,
        QKeyValue.FindIntAttribute(impl.Attributes, "kInductionDepth", -1));
      if (k < 0)
      {
        ConvertCFG2DAGStandard(impl, edgesCut, taskID);
      }
      else
      {
        ConvertCFG2DAGKInduction(impl, edgesCut, taskID, k);
      }

      #region Debug Tracing

      if (Options.TraceVerify)
      {
        run.OutputWriter.WriteLine("after conversion into a DAG");
        EmitImpl(Options, run, true);
      }

      #endregion
    }

    private void ConvertCFG2DAGStandard(Implementation impl, Dictionary<Block, List<Block>> edgesCut, int taskID)
    {
      #region Convert program CFG into a DAG

      #region Use the graph library to figure out where the (natural) loops are

      #region Create the graph by adding the source node and each edge

      Graph<Block> g = Program.GraphFromImpl(impl);

      #endregion

      //Graph<Block> g = program.ProcessLoops(impl);

      g.ComputeLoops(); // this is the call that does all of the processing
      if (!g.Reducible)
      {
        throw new VCGenException("Irreducible flow graphs are unsupported.");
      }

      #endregion

      #region Cut the backedges, push assert/assume statements from loop header into predecessors, change them all into assume statements at top of loop, introduce havoc statements

      foreach (Block header in cce.NonNull(g.Headers))
      {
        Contract.Assert(header != null);
        IDictionary<Block, object> backEdgeNodes = new Dictionary<Block, object>();
        foreach (Block b in cce.NonNull(g.BackEdgeNodes(header)))
        {
          Contract.Assert(b != null);
          backEdgeNodes.Add(b, null);
        }

        #region Find the (possibly empty) prefix of assert commands in the header, replace each assert with an assume of the same condition

        List<Cmd> prefixOfPredicateCmdsInit = new List<Cmd>();
        List<Cmd> prefixOfPredicateCmdsMaintained = new List<Cmd>();
        for (int i = 0, n = header.Cmds.Count; i < n; i++)
        {
          PredicateCmd predicateCmd = header.Cmds[i] as PredicateCmd;
          if (predicateCmd != null)
          {
            if (predicateCmd is AssertCmd)
            {
              AssertCmd assertCmd = (AssertCmd)predicateCmd;
              AssertCmd initAssertCmd = null;

              if (Options.ConcurrentHoudini)
              {
                Contract.Assert(taskID >= 0);
                if (Options.Cho[taskID].DisableLoopInvEntryAssert)
                {
                  initAssertCmd = new LoopInitAssertCmd(assertCmd.tok, Expr.True, assertCmd);
                }
                else
                {
                  initAssertCmd = new LoopInitAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
                }
              }
              else
              {
                initAssertCmd = new LoopInitAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
              }

              initAssertCmd.Attributes = (QKeyValue)assertCmd.Attributes?.Clone();
              // Copy any {:id ...} from the invariant to the assertion that it's established, so
              // we can track it while analyzing verification coverage.
              (initAssertCmd as ICarriesAttributes).CopyIdWithModificationsFrom(assertCmd.tok, assertCmd,
                id => new TrackedInvariantEstablished(id));

              prefixOfPredicateCmdsInit.Add(initAssertCmd);

              LoopInvMaintainedAssertCmd maintainedAssertCmd;
              if (Options.ConcurrentHoudini)
              {
                Contract.Assert(taskID >= 0);
                if (Options.Cho[taskID].DisableLoopInvMaintainedAssert)
                {
                  maintainedAssertCmd = new Bpl.LoopInvMaintainedAssertCmd(assertCmd.tok, Expr.True, assertCmd);
                }
                else
                {
                  maintainedAssertCmd = new Bpl.LoopInvMaintainedAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
                }
              }
              else
              {
                maintainedAssertCmd = new Bpl.LoopInvMaintainedAssertCmd(assertCmd.tok, assertCmd.Expr, assertCmd);
              }

              maintainedAssertCmd.Attributes = (QKeyValue)assertCmd.Attributes?.Clone();
              // Copy any {:id ...} from the invariant to the assertion that it's maintained, so
              // we can track it while analyzing verification coverage.
              (maintainedAssertCmd as ICarriesAttributes).CopyIdWithModificationsFrom(assertCmd.tok, assertCmd,
                id => new TrackedInvariantMaintained(id));

              prefixOfPredicateCmdsMaintained.Add(maintainedAssertCmd);
              AssumeCmd assume = new AssumeCmd(assertCmd.tok, assertCmd.Expr);
              // Copy any {:id ...} from the invariant to the assumption used within the body, so
              // we can track it while analyzing verification coverage.
              (assume as ICarriesAttributes).CopyIdWithModificationsFrom(assertCmd.tok, assertCmd,
                id => new TrackedInvariantAssumed(id));

              header.Cmds[i] = assume;
            }
            else
            {
              Contract.Assert(predicateCmd is AssumeCmd);
              if (Options.AlwaysAssumeFreeLoopInvariants)
              {
                // Usually, "free" stuff, like free loop invariants (and the assume statements
                // that stand for such loop invariants) are ignored on the checking side.  This
                // command-line option changes that behavior to always assume the conditions.
                prefixOfPredicateCmdsInit.Add(predicateCmd);
                prefixOfPredicateCmdsMaintained.Add(predicateCmd);
              }
            }
          }
          else if (header.Cmds[i] is CommentCmd)
          {
            // ignore
          }
          else
          {
            break; // stop when an assignment statement (or any other non-predicate cmd) is encountered
          }
        }

        #endregion

        #region Copy the prefix of predicate commands into each predecessor. Do this *before* cutting the backedge!!

        for (int predIndex = 0, n = header.Predecessors.Count; predIndex < n; predIndex++)
        {
          Block pred = cce.NonNull(header.Predecessors[predIndex]);

          // Create a block between header and pred for the predicate commands if pred has more than one successor
          GotoCmd gotocmd = cce.NonNull((GotoCmd)pred.TransferCmd);
          Contract.Assert(gotocmd.labelNames !=
                          null); // if "pred" is really a predecessor, it may be a GotoCmd with at least one label
          if (gotocmd.labelNames.Count > 1)
          {
            Block newBlock = CreateBlockBetween(predIndex, header);
            impl.Blocks.Add(newBlock);

            // if pred is a back edge node, then now newBlock is the back edge node
            if (backEdgeNodes.ContainsKey(pred))
            {
              backEdgeNodes.Remove(pred);
              backEdgeNodes.Add(newBlock, null);
            }

            pred = newBlock;
          }

          // Add the predicate commands
          if (backEdgeNodes.ContainsKey(pred))
          {
            pred.Cmds.AddRange(prefixOfPredicateCmdsMaintained);
          }
          else
          {
            pred.Cmds.AddRange(prefixOfPredicateCmdsInit);
          }
        }

        #endregion

        #region Cut the back edge

        foreach (Block backEdgeNode in cce.NonNull(backEdgeNodes.Keys))
        {
          Contract.Assert(backEdgeNode != null);
          Debug.Assert(backEdgeNode.TransferCmd is GotoCmd,
            "An node was identified as the source for a backedge, but it does not have a goto command.");
          GotoCmd gtc = backEdgeNode.TransferCmd as GotoCmd;
          if (gtc != null && gtc.labelTargets != null && gtc.labelTargets.Count > 1)
          {
            // then remove the backedge by removing the target block from the list of gotos
            List<Block> remainingTargets = new List<Block>();
            List<String> remainingLabels = new List<String>();
            Contract.Assume(gtc.labelNames != null);
            for (int i = 0, n = gtc.labelTargets.Count; i < n; i++)
            {
              if (gtc.labelTargets[i] != header)
              {
                remainingTargets.Add(gtc.labelTargets[i]);
                remainingLabels.Add(gtc.labelNames[i]);
              }
              else
              {
                RecordCutEdge(edgesCut, backEdgeNode, header);
              }
            }

            gtc.labelTargets = remainingTargets;
            gtc.labelNames = remainingLabels;
          }
          else
          {
            // This backedge is the only out-going edge from this node.
            // Add an "assume false" statement to the end of the statements
            // inside of the block and change the goto command to a return command.
            AssumeCmd ac = new AssumeCmd(Token.NoToken, Expr.False);
            backEdgeNode.Cmds.Add(ac);
            backEdgeNode.TransferCmd = new ReturnCmd(Token.NoToken);
            if (gtc != null && gtc.labelTargets != null && gtc.labelTargets.Count == 1)
            {
              RecordCutEdge(edgesCut, backEdgeNode, gtc.labelTargets[0]);
            }
          }

          #region Remove the backedge node from the list of predecessor nodes in the header

          List<Block> newPreds = new List<Block>();
          foreach (Block p in header.Predecessors)
          {
            if (p != backEdgeNode)
            {
              newPreds.Add(p);
            }
          }

          header.Predecessors = newPreds;

          #endregion
        }

        #endregion

        #region Collect all variables that are assigned to in all of the natural loops for which this is the header

        List<Variable> varsToHavoc = VarsAssignedInLoop(g, header);
        List<IdentifierExpr> havocExprs = new List<IdentifierExpr>();
        foreach (Variable v in varsToHavoc)
        {
          Contract.Assert(v != null);
          IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
          if (!havocExprs.Contains(ie))
          {
            havocExprs.Add(ie);
          }
        }

        // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
        // the source location for this later on
        HavocCmd hc = new HavocCmd(header.tok, havocExprs);
        List<Cmd> newCmds = new List<Cmd>();
        newCmds.Add(hc);
        foreach (Cmd c in header.Cmds)
        {
          newCmds.Add(c);
        }

        header.Cmds = newCmds;

        #endregion
      }

      #endregion

      #endregion Convert program CFG into a DAG
    }

    public static List<Variable> VarsAssignedInLoop(Graph<Block> g, Block header)
    {
      List<Variable> varsToHavoc = new List<Variable>();
      foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
      {
        Contract.Assert(backEdgeNode != null);
        foreach (Block b in g.NaturalLoops(header, backEdgeNode))
        {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds)
          {
            Contract.Assert(c != null);
            c.AddAssignedVariables(varsToHavoc);
          }
        }
      }

      return varsToHavoc;
    }

    public static IEnumerable<Variable> VarsReferencedInLoop(Graph<Block> g, Block header)
    {
      HashSet<Variable> referencedVars = new HashSet<Variable>();
      foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
      {
        Contract.Assert(backEdgeNode != null);
        foreach (Block b in g.NaturalLoops(header, backEdgeNode))
        {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds)
          {
            Contract.Assert(c != null);
            var Collector = new VariableCollector();
            Collector.Visit(c);
            foreach (var v in Collector.usedVars)
            {
              referencedVars.Add(v);
            }
          }
        }
      }

      return referencedVars;
    }

    private void ConvertCFG2DAGKInduction(Implementation impl, Dictionary<Block, List<Block>> edgesCut, int taskID,
      int inductionK)
    {
      // K-induction has not been adapted to be aware of these parameters which standard CFG to DAG transformation uses
      Contract.Requires(edgesCut == null);
      Contract.Requires(taskID == -1);
      Contract.Requires(0 <= inductionK);

      bool contRuleApplication = true;
      while (contRuleApplication)
      {
        contRuleApplication = false;

        #region Use the graph library to figure out where the (natural) loops are

        #region Create the graph by adding the source node and each edge

        Graph<Block> g = Program.GraphFromImpl(impl);

        #endregion

        g.ComputeLoops(); // this is the call that does all of the processing
        if (!g.Reducible)
        {
          throw new VCGenException("Irreducible flow graphs are unsupported.");
        }

        #endregion

        foreach (Block header in cce.NonNull(g.Headers))
        {
          Contract.Assert(header != null);

          #region Debug Tracing

          if (Options.TraceVerify)
          {
            Options.OutputWriter.WriteLine("Applying k-induction rule with k=" + inductionK);
          }

          #endregion

          #region generate the step case

          Block newHeader = DuplicateLoop(impl, g, header, null,
            false, false, "_step_assertion");
          for (int i = 0; i < inductionK; ++i)
          {
            newHeader = DuplicateLoop(impl, g, header, newHeader,
              true, true,
              "_step_" + (inductionK - i));
          }

          #endregion

          #region havoc variables that can be assigned in the loop

          List<Variable> varsToHavoc = VarsAssignedInLoop(g, header);
          List<IdentifierExpr> havocExprs = new List<IdentifierExpr>();
          foreach (Variable v in varsToHavoc)
          {
            Contract.Assert(v != null);
            IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
            if (!havocExprs.Contains(ie))
            {
              havocExprs.Add(ie);
            }
          }

          // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
          // the source location for this later on
          HavocCmd hc = new HavocCmd(newHeader.tok, havocExprs);
          List<Cmd> havocCmds = new List<Cmd>();
          havocCmds.Add(hc);

          Block havocBlock = new Block(newHeader.tok, newHeader.Label + "_havoc", havocCmds,
            new GotoCmd(newHeader.tok, new List<Block> { newHeader }));

          impl.Blocks.Add(havocBlock);
          newHeader.Predecessors.Add(havocBlock);
          newHeader = havocBlock;

          #endregion

          #region generate the base case loop copies

          for (int i = 0; i < inductionK; ++i)
          {
            newHeader = DuplicateLoop(impl, g, header, newHeader,
              false, false,
              "_base_" + (inductionK - i));
          }

          #endregion

          #region redirect into the new loop copies and remove the original loop (but don't redirect back-edges)

          IDictionary<Block, object> backEdgeNodes = new Dictionary<Block, object>();
          foreach (Block b in cce.NonNull(g.BackEdgeNodes(header)))
          {
            Contract.Assert(b != null);
            backEdgeNodes.Add(b, null);
          }

          for (int predIndex = 0, n = header.Predecessors.Count(); predIndex < n; predIndex++)
          {
            Block pred = cce.NonNull(header.Predecessors[predIndex]);
            if (!backEdgeNodes.ContainsKey(pred))
            {
              GotoCmd gc = pred.TransferCmd as GotoCmd;
              Contract.Assert(gc != null);
              for (int i = 0; i < gc.labelTargets.Count(); ++i)
              {
                if (gc.labelTargets[i] == header)
                {
                  gc.labelTargets[i] = newHeader;
                  gc.labelNames[i] = newHeader.Label;
                  newHeader.Predecessors.Add(pred);
                }
              }
            }
          }

          impl.PruneUnreachableBlocks(Options);

          #endregion

          contRuleApplication = true;
          break;
        }
      }

      ResetPredecessors(impl.Blocks);
      impl.FreshenCaptureStates();
    }

    private Block DuplicateLoop(Implementation impl, Graph<Block> g,
      Block header, Block nextHeader, bool cutExits,
      bool toAssumptions, string suffix)
    {
      IDictionary<Block, Block> ori2CopiedBlocks = new Dictionary<Block, Block>();
      Duplicator duplicator = new Duplicator();

      #region create copies of all blocks in the loop

      foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
      {
        Contract.Assert(backEdgeNode != null);
        foreach (Block b in g.NaturalLoops(header, backEdgeNode))
        {
          Contract.Assert(b != null);
          if (!ori2CopiedBlocks.ContainsKey(b))
          {
            Block copy = (Block)duplicator.Visit(b);
            copy.Cmds = new List<Cmd>(copy
              .Cmds); // Philipp Ruemmer commented that this was necessary due to a bug in the Duplicator.  That was a long time; worth checking whether this has been fixed
            copy.Predecessors = new List<Block>();
            copy.Label = copy.Label + suffix;

            #region turn asserts into assumptions

            if (toAssumptions)
            {
              for (int i = 0; i < copy.Cmds.Count(); ++i)
              {
                AssertCmd ac = copy.Cmds[i] as AssertCmd;
                if (ac != null)
                {
                  copy.Cmds[i] = new AssumeCmd(ac.tok, ac.Expr);
                }
              }
            }

            #endregion

            impl.Blocks.Add(copy);
            ori2CopiedBlocks.Add(b, copy);
          }
        }
      }

      #endregion

      #region adjust the transfer commands of the newly created blocks

      foreach (KeyValuePair<Block, Block> pair in ori2CopiedBlocks)
      {
        Block copy = pair.Value;
        GotoCmd gc = copy.TransferCmd as GotoCmd;
        if (gc != null)
        {
          List<Block> newTargets = new List<Block>();
          List<string> newLabels = new List<string>();

          for (int i = 0; i < gc.labelTargets.Count(); ++i)
          {
            if (gc.labelTargets[i] == header)
            {
              if (nextHeader != null)
              {
                newTargets.Add(nextHeader);
                newLabels.Add(nextHeader.Label);
                nextHeader.Predecessors.Add(copy);
              }
            }
            else if (ori2CopiedBlocks.TryGetValue(gc.labelTargets[i], out var newTarget))
            {
              newTargets.Add(newTarget);
              newLabels.Add(newTarget.Label);
              newTarget.Predecessors.Add(copy);
            }
            else if (!cutExits)
            {
              newTargets.Add(gc.labelTargets[i]);
              newLabels.Add(gc.labelNames[i]);
              gc.labelTargets[i].Predecessors.Add(copy);
            }
          }

          if (newTargets.Count() == 0)
          {
            // if no targets are left, we assume false and return
            copy.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            copy.TransferCmd = new ReturnCmd(Token.NoToken);
          }
          else
          {
            copy.TransferCmd = new GotoCmd(gc.tok, newLabels, newTargets);
          }
        }
        else if (cutExits && (copy.TransferCmd is ReturnCmd))
        {
          // because return is a kind of exit from the loop, we
          // assume false to cut this path
          copy.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
        }
      }

      #endregion

      return ori2CopiedBlocks[header];
    }

    public void DesugarCalls(Implementation impl)
    {
      foreach (Block block in impl.Blocks)
      {
        List<Cmd> newCmds = new List<Cmd>();
        foreach (Cmd cmd in block.Cmds)
        {
          SugaredCmd sugaredCmd = cmd as SugaredCmd;
          if (sugaredCmd != null)
          {
            StateCmd stateCmd = sugaredCmd.GetDesugaring(Options) as StateCmd;
            foreach (Variable v in stateCmd.Locals)
            {
              impl.LocVars.Add(v);
            }

            newCmds.AddRange(stateCmd.Cmds);
          }
          else
          {
            newCmds.Add(cmd);
          }
        }

        block.Cmds = newCmds;
      }
    }

    public Dictionary<TransferCmd, ReturnCmd> PassifyImpl(ImplementationRun run, out ModelViewInfo modelViewInfo)
    {
      Contract.Requires(run != null);
      Contract.Requires(program != null);
      Contract.Ensures(Contract.Result<Dictionary<TransferCmd, ReturnCmd>>() != null);

      var impl = run.Implementation;
      Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
      Block exitBlock = GenerateUnifiedExit(impl, gotoCmdOrigins);

      #region Debug Tracing

      if (Options.TraceVerify)
      {
        Options.OutputWriter.WriteLine("after creating a unified exit block");
        EmitImpl(Options, run, true);
      }

      #endregion

      #region Insert pre- and post-conditions and where clauses as assume and assert statements

      {
        List<Cmd> cc = new List<Cmd>();
        // where clauses of global variables
        lock (program.TopLevelDeclarations)
        {
          foreach (var gvar in program.GlobalVariables)
          {
            if (gvar != null && gvar.TypedIdent.WhereExpr != null)
            {
              Cmd c = new AssumeCmd(gvar.tok, gvar.TypedIdent.WhereExpr);
              cc.Add(c);
            }
          }
        }

        // where clauses of in- and out-parameters
        cc.AddRange(GetParamWhereClauses(Options, run));
        // where clauses of local variables
        foreach (Variable lvar in impl.LocVars)
        {
          Contract.Assert(lvar != null);
          var idExp = new IdentifierExpr(lvar.tok, lvar);
          if (lvar.TypedIdent.WhereExpr != null)
          {
            var exp = Expr.Binary(lvar.tok, BinaryOperator.Opcode.And, lvar.TypedIdent.WhereExpr,
              LiteralExpr.Literal(true));
            Cmd c = new AssumeCmd(lvar.tok, exp,
              new QKeyValue(lvar.tok, "where", new List<object>(new object[] { idExp }), null));
            cc.Add(c);
          }
          else if (QKeyValue.FindBoolAttribute(lvar.Attributes, "assumption"))
          {
            cc.Add(new AssumeCmd(lvar.tok, idExp,
              new QKeyValue(lvar.tok, "assumption_variable_initialization", new List<object>(), null)));
          }
        }

        // add cc and the preconditions to new blocks preceding impl.Blocks[0]
        InjectPreconditions(Options, run, cc);

        // append postconditions, starting in exitBlock and continuing into other blocks, if needed
        InjectPostConditions(Options, run, exitBlock, gotoCmdOrigins);
      }

      #endregion

      #region Support for stratified inlining

      AddExitAssert(impl.Name, exitBlock);

      #endregion


      #region Debug Tracing

      if (Options.TraceVerify)
      {
        Options.OutputWriter.WriteLine("after inserting pre- and post-conditions");
        EmitImpl(Options, run, true);
      }

      #endregion

      AddBlocksBetween(impl.Blocks);

      #region Debug Tracing

      if (Options.TraceVerify)
      {
        Options.OutputWriter.WriteLine("after adding empty blocks as needed to catch join assumptions");
        EmitImpl(Options, run, true);
      }

      #endregion

      if (Options.LiveVariableAnalysis > 0)
      {
        new LiveVariableAnalysis(Options).ComputeLiveVariables(impl);
      }

      modelViewInfo = new ModelViewInfo(program, impl);
      Convert2PassiveCmd(run, modelViewInfo);

      if (QKeyValue.FindBoolAttribute(impl.Attributes, "may_unverified_instrumentation"))
      {
        InstrumentWithMayUnverifiedConditions(impl, exitBlock);
      }

      #region Peep-hole optimizations

      if (Options.RemoveEmptyBlocks)
      {
        #region Get rid of empty blocks

        {
          RemoveEmptyBlocks(impl.Blocks);
          impl.PruneUnreachableBlocks(Options);
        }

        #endregion Get rid of empty blocks

        #region Debug Tracing

        if (Options.TraceVerify)
        {
          Options.OutputWriter.WriteLine("after peep-hole optimizations");
          EmitImpl(Options, run, true);
        }

        #endregion
      }

      #endregion Peep-hole optimizations

      HandleSelectiveChecking(impl);


//      #region Constant Folding
//      #endregion
//      #region Debug Tracing
//      if (CommandLineOptions.Clo.TraceVerify)
//      {
//        Console.WriteLine("after constant folding");
//        EmitImpl(impl, true);
//      }
//      #endregion

      return gotoCmdOrigins;
    }

    #region Simplified May-Unverified Analysis and Instrumentation

    static void InstrumentWithMayUnverifiedConditions(Implementation impl, Block unifiedExitBlock)
    {
      var q = new Queue<Block>();
      q.Enqueue(unifiedExitBlock);
      var conditionOnBlockEntry = new Dictionary<Block, HashSet<Variable>>();
      while (q.Any())
      {
        var block = q.Dequeue();

        if (conditionOnBlockEntry.ContainsKey(block))
        {
          continue;
        }

        var gotoCmd = block.TransferCmd as GotoCmd;
        if (gotoCmd != null && gotoCmd.labelTargets.Any(b => !conditionOnBlockEntry.ContainsKey(b)))
        {
          q.Enqueue(block);
          continue;
        }

        HashSet<Variable> cond = new HashSet<Variable>();
        if (gotoCmd != null)
        {
          var mayInstrs = new List<Block>();
          bool noInstr = true;
          foreach (var succ in gotoCmd.labelTargets)
          {
            var c = conditionOnBlockEntry[succ];
            if (c != null)
            {
              mayInstrs.Add(succ);
            }
            else
            {
              noInstr = false;
            }

            cond = JoinVariableSets(cond, c);
          }

          if (!noInstr)
          {
            foreach (var instr in mayInstrs)
            {
              InstrumentWithCondition(instr, 0, conditionOnBlockEntry[instr]);
            }
          }
        }

        for (int i = block.Cmds.Count - 1; 0 <= i; i--)
        {
          var cmd = block.Cmds[i];
          if (cond == null)
          {
            break;
          }

          var assertCmd = cmd as AssertCmd;
          if (assertCmd != null)
          {
            var litExpr = assertCmd.Expr as LiteralExpr;
            if (litExpr != null && litExpr.IsTrue)
            {
              continue;
            }

            HashSet<Variable> vu = null;
            if (assertCmd.VerifiedUnder == null)
            {
              vu = null;
            }
            else
            {
              if (IsConjunctionOfAssumptionVariables(assertCmd.VerifiedUnder, out var vars))
              {
                vu = vars;
                // TODO(wuestholz): Maybe drop the :verified_under attribute.
              }
              else
              {
                vu = null;
              }
            }

            if (vu == null)
            {
              InstrumentWithCondition(block, i + 1, cond);
            }

            cond = JoinVariableSets(cond, vu);
          }
        }

        if (cond != null && block.Predecessors.Count == 0)
        {
          // TODO(wuestholz): Should we rather instrument each block?
          InstrumentWithCondition(block, 0, cond);
        }

        foreach (var pred in block.Predecessors)
        {
          q.Enqueue(pred);
        }

        conditionOnBlockEntry[block] = cond;
      }
    }

    private static void InstrumentWithCondition(Block block, int idx, HashSet<Variable> condition)
    {
      var conj = Expr.BinaryTreeAnd(condition.Select(v => (Expr)new IdentifierExpr(Token.NoToken, v)).ToList());
      block.Cmds.Insert(idx, new AssumeCmd(Token.NoToken, Expr.Not(conj)));
    }

    static HashSet<Variable> JoinVariableSets(HashSet<Variable> c0, HashSet<Variable> c1)
    {
      // We use the following lattice:
      // - Top: null (i.e., true)
      // - Bottom: new HashSet<Variable>() (i.e., false)
      // - Other Elements: new HashSet<Variable>(...) (i.e., conjunctions of assumption variables)

      if (c0 == null || c1 == null)
      {
        return null;
      }

      var result = new HashSet<Variable>(c0);
      result.UnionWith(c1);
      return result;
    }

    static bool IsAssumptionVariableOrIncarnation(Variable v)
    {
      if (QKeyValue.FindBoolAttribute(v.Attributes, "assumption"))
      {
        return true;
      }

      var incar = v as Incarnation;
      return incar == null || QKeyValue.FindBoolAttribute(incar.OriginalVariable.Attributes, "assumption");
    }

    static bool IsConjunctionOfAssumptionVariables(Expr expr, out HashSet<Variable> variables)
    {
      Contract.Requires(expr != null);

      variables = null;
      var litExpr = expr as LiteralExpr;
      if (litExpr != null && (litExpr.IsFalse || litExpr.IsTrue))
      {
        if (litExpr.IsTrue)
        {
          variables = new HashSet<Variable>();
        }

        return true;
      }

      var idExpr = expr as IdentifierExpr;
      if (idExpr != null && IsAssumptionVariableOrIncarnation(idExpr.Decl))
      {
        variables = new HashSet<Variable>();
        variables.Add(idExpr.Decl);
        return true;
      }

      var andExpr = expr as NAryExpr;
      if (andExpr != null)
      {
        var fun = andExpr.Fun as BinaryOperator;
        if (fun != null && fun.Op == BinaryOperator.Opcode.And && andExpr.Args != null)
        {
          bool res = true;
          variables = new HashSet<Variable>();
          foreach (var op in andExpr.Args)
          {
            var r = IsConjunctionOfAssumptionVariables(op, out var vars);
            res &= r;
            variables = JoinVariableSets(variables, vars);
            if (!res)
            {
              break;
            }
          }

          return res;
        }
      }

      return false;
    }

    #endregion

    private void HandleSelectiveChecking(Implementation impl)
    {
      if (QKeyValue.FindBoolAttribute(impl.Attributes, "selective_checking") ||
          QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "selective_checking"))
      {
        var startPoints = new List<Block>();
        foreach (var b in impl.Blocks)
        {
          foreach (Cmd c in b.Cmds)
          {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "start_checking_here"))
            {
              startPoints.Add(b);
              break;
            }
          }
        }

        // Compute the set of blocks reachable from blocks containing "start_checking_here"
        var blocksToCheck = new HashSet<Block>();
        foreach (var b in startPoints)
        {
          var todo = new Stack<Block>();
          var wasThere = blocksToCheck.Contains(b);
          todo.Push(b);
          while (todo.Count > 0)
          {
            var x = todo.Pop();
            if (blocksToCheck.Contains(x))
            {
              continue;
            }

            blocksToCheck.Add(x);
            var ex = x.TransferCmd as GotoCmd;
            if (ex != null)
            {
              foreach (Block e in ex.labelTargets)
              {
                todo.Push(e);
              }
            }
          }

          if (!wasThere)
          {
            blocksToCheck.Remove(b);
          }
        }

        // Convert asserts to assumes in "unreachable" blocks, as well as in portions of blocks before we reach "start_checking_here"
        foreach (var b in impl.Blocks)
        {
          if (blocksToCheck.Contains(b))
          {
            continue; // All reachable blocks must be checked in their entirety, so don't change anything
          }

          var newCmds = new List<Cmd>();
          var copyMode = false;
          foreach (Cmd c in b.Cmds)
          {
            var p = c as PredicateCmd;
            if (p != null && QKeyValue.FindBoolAttribute(p.Attributes, "start_checking_here"))
            {
              copyMode = true;
            }

            var asrt = c as AssertCmd;
            if (copyMode || asrt == null)
            {
              newCmds.Add(c);
            }
            else
            {
              newCmds.Add(AssertTurnedIntoAssume(Options, asrt));
            }
          }

          b.Cmds = newCmds;
        }
      }
    }

    // Used by stratified inlining
    protected virtual void AddExitAssert(string implName, Block exitBlock)
    {
    }

    public virtual Counterexample ExtractLoopTrace(Counterexample cex, string mainProcName, Program program,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
      // Construct the set of inlined procs in the original program
      var inlinedProcs = new HashSet<string>();
      foreach (var proc in program.Procedures)
      {
        if (!(proc is LoopProcedure))
        {
          inlinedProcs.Add(proc.Name);
        }
      }

      return ExtractLoopTraceRec(
        new CalleeCounterexampleInfo(cex, new List<object>()),
        mainProcName, inlinedProcs, extractLoopMappingInfo).counterexample;
    }

    protected CalleeCounterexampleInfo ExtractLoopTraceRec(
      CalleeCounterexampleInfo cexInfo, string currProc,
      HashSet<string> inlinedProcs,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
      Contract.Requires(currProc != null);
      if (cexInfo.counterexample == null)
      {
        return cexInfo;
      }

      var cex = cexInfo.counterexample;
      // Go through all blocks in the trace, map them back to blocks in the original program (if there is one)
      var ret = cex.Clone();
      ret.Trace = new List<Block>();
      ret.calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();

      for (int numBlock = 0; numBlock < cex.Trace.Count; numBlock++)
      {
        Block block = cex.Trace[numBlock];
        var origBlock = ProcGetBlock(currProc, block, extractLoopMappingInfo);
        if (origBlock != null)
        {
          ret.Trace.Add(origBlock);
        }

        var callCnt = 1;
        for (int numInstr = 0; numInstr < block.Cmds.Count; numInstr++)
        {
          Cmd cmd = block.Cmds[numInstr];
          var loc = new TraceLocation(numBlock, numInstr);
          if (!cex.calleeCounterexamples.ContainsKey(loc))
          {
            if (GetCallee(cex.GetTraceCmd(loc), inlinedProcs) != null)
            {
              callCnt++;
            }

            continue;
          }

          string callee = cex.GetCalledProcName(cex.GetTraceCmd(loc));
          Contract.Assert(callee != null);
          var calleeTrace = cex.calleeCounterexamples[loc];
          Debug.Assert(calleeTrace != null);

          var origTrace = ExtractLoopTraceRec(calleeTrace, callee, inlinedProcs, extractLoopMappingInfo);

          if (ProcIsLoop(callee))
          {
            // Absorb the trace into the current trace

            int currLen = ret.Trace.Count;
            ret.Trace.AddRange(origTrace.counterexample.Trace);

            foreach (var kvp in origTrace.counterexample.calleeCounterexamples)
            {
              var newloc = new TraceLocation(kvp.Key.numBlock + currLen, kvp.Key.numInstr);
              ret.calleeCounterexamples.Add(newloc, kvp.Value);
            }
          }
          else
          {
            var origLoc = new TraceLocation(ret.Trace.Count - 1,
              GetCallCmdPosition(origBlock, callCnt, inlinedProcs, callee));
            ret.calleeCounterexamples.Add(origLoc, origTrace);
            callCnt++;
          }
        }
      }

      return new CalleeCounterexampleInfo(ret, cexInfo.args);
    }

    // return the position of the i^th CallCmd in the block (count only those Calls that call a procedure in inlinedProcs).
    // Assert failure if there isn't any.
    // Assert that the CallCmd found calls "callee"
    private int GetCallCmdPosition(Block block, int i, HashSet<string> inlinedProcs, string callee)
    {
      Debug.Assert(i >= 1);
      for (int pos = 0; pos < block.Cmds.Count; pos++)
      {
        Cmd cmd = block.Cmds[pos];
        string procCalled = GetCallee(cmd, inlinedProcs);

        if (procCalled != null)
        {
          if (i == 1)
          {
            Debug.Assert(procCalled == callee);
            return pos;
          }

          i--;
        }
      }

      Debug.Assert(false, "Didn't find the i^th call cmd");
      return -1;
    }

    private string GetCallee(Cmd cmd, HashSet<string> inlinedProcs)
    {
      string procCalled = null;
      if (cmd is CallCmd)
      {
        var cc = (CallCmd)cmd;
        if (inlinedProcs.Contains(cc.Proc.Name))
        {
          procCalled = cc.Proc.Name;
        }
      }

      if (cmd is AssumeCmd)
      {
        var expr = (cmd as AssumeCmd).Expr as NAryExpr;
        if (expr != null)
        {
          if (inlinedProcs.Contains(expr.Fun.FunctionName))
          {
            procCalled = expr.Fun.FunctionName;
          }
        }
      }

      return procCalled;
    }

    protected virtual bool ProcIsLoop(string procname)
    {
      return false;
    }

    private Block ProcGetBlock(string procname, Block block,
      Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
    {
      Contract.Requires(procname != null);

      if (!extractLoopMappingInfo.ContainsKey(procname))
      {
        return block;
      }

      if (!extractLoopMappingInfo[procname].ContainsKey(block.Label))
      {
        return null;
      }

      return extractLoopMappingInfo[procname][block.Label];
    }

    static Counterexample TraceCounterexample(
      VCGenOptions options,
      Block b, HashSet<Absy> traceNodes, List<Block> trace, Model errModel, ModelViewInfo mvInfo,
      Dictionary<Cmd, List<object>> debugInfos,
      ProverContext context,
      ProofRun split,
      Dictionary<TraceLocation, CalleeCounterexampleInfo> calleeCounterexamples)
    {
      Contract.Requires(b != null);
      Contract.Requires(traceNodes != null);
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(calleeCounterexamples));
      // After translation, all potential errors come from asserts.

      List<object> augmentedTrace = new List<object>();
      while (true)
      {
        List<Cmd> cmds = b.Cmds;
        Contract.Assert(cmds != null);
        TransferCmd transferCmd = cce.NonNull(b.TransferCmd);
        for (int i = 0; i < cmds.Count; i++)
        {
          Cmd cmd = cce.NonNull(cmds[i]);

          // update augmentedTrace
          if (errModel != null && debugInfos != null && debugInfos.ContainsKey(cmd))
          {
            augmentedTrace.AddRange(debugInfos[cmd]);
          }

          // Skip if 'cmd' not contained in the trace or not an assert
          if (cmd is AssertCmd && traceNodes.Contains(cmd))
          {
            Counterexample newCounterexample =
              AssertCmdToCounterexample(options, (AssertCmd)cmd, transferCmd, trace, augmentedTrace, errModel, mvInfo,
                context, split);
            Contract.Assert(newCounterexample != null);
            newCounterexample.AddCalleeCounterexample(calleeCounterexamples);
            return newCounterexample;
          }
        }

        GotoCmd gotoCmd = transferCmd as GotoCmd;
        if (gotoCmd == null)
        {
          return null;
        }

        Block foundBlock = null;
        foreach (Block bb in cce.NonNull(gotoCmd.labelTargets))
        {
          Contract.Assert(bb != null);
          if (traceNodes.Contains(bb))
          {
            foundBlock = bb;
            break;
          }
        }

        if (foundBlock == null)
        {
          return null;
        }

        trace.Add(foundBlock);
        b = foundBlock;
      }
    }

    public static Counterexample AssertCmdToCounterexample(VCGenOptions options, AssertCmd cmd, TransferCmd transferCmd,
      List<Block> trace, List<object> augmentedTrace,
      Model errModel, ModelViewInfo mvInfo, ProverContext context, ProofRun split)
    {
      Contract.Requires(cmd != null);
      Contract.Requires(transferCmd != null);
      Contract.Requires(trace != null);
      Contract.Requires(context != null);
      Contract.Ensures(Contract.Result<Counterexample>() != null);

      // See if it is a special assert inserted in translation
      if (cmd is AssertRequiresCmd)
      {
        AssertRequiresCmd assertCmd = (AssertRequiresCmd)cmd;
        Contract.Assert(assertCmd != null);
        CallCounterexample cc = new CallCounterexample(options, trace, augmentedTrace, assertCmd, errModel, mvInfo,
          context, split, assertCmd.Checksum);
        return cc;
      }
      else if (cmd is AssertEnsuresCmd)
      {
        AssertEnsuresCmd assertCmd = (AssertEnsuresCmd)cmd;
        Contract.Assert(assertCmd != null);
        ReturnCounterexample rc = new ReturnCounterexample(options, trace, augmentedTrace, assertCmd, transferCmd,
          errModel, mvInfo,
          context, split, cmd.Checksum);
        return rc;
      }
      else
      {
        AssertCounterexample ac = new AssertCounterexample(options, trace, augmentedTrace, (AssertCmd)cmd, errModel,
          mvInfo, context, split);
        return ac;
      }
    }

    /// <summary>
    /// Returns a clone of "cex", but with the location stored in "cex" replaced by those from "assrt".
    /// </summary>
    public static Counterexample AssertCmdToCloneCounterexample(VCGenOptions options, AssertCmd assrt,
      Counterexample cex,
      Block implEntryBlock, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins)
    {
      Contract.Requires(assrt != null);
      Contract.Requires(cex != null);
      Contract.Requires(implEntryBlock != null);
      Contract.Requires(gotoCmdOrigins != null);
      Contract.Ensures(Contract.Result<Counterexample>() != null);

      Counterexample cc;
      if (assrt is AssertRequiresCmd)
      {
        var aa = (AssertRequiresCmd)assrt;
        cc = new CallCounterexample(options, cex.Trace, cex.AugmentedTrace, aa, cex.Model, cex.MvInfo, cex.Context,
          cex.ProofRun, aa.Checksum);
      }
      else if (assrt is AssertEnsuresCmd && cex is ReturnCounterexample)
      {
        var aa = (AssertEnsuresCmd)assrt;
        var oldCex = (ReturnCounterexample)cex;
        // The first three parameters of ReturnCounterexample are: List<Block> trace, List<object> augmentedTrace, TransferCmd failingReturn, Ensures failingEnsures.
        // We have the "aa" version of failingEnsures, namely aa.Ensures.  The first and third parameters take more work to reconstruct.
        // (The code here assumes the labels of blocks remain the same. If that's not the case, then it is possible that the trace
        // computed does not lead to where the error is, but at least the error will not be masked.)
        List<Block> reconstructedTrace = null;
        Block prevBlock = null;
        foreach (var blk in cex.Trace)
        {
          if (reconstructedTrace == null)
          {
            if (implEntryBlock.Label != blk.Label)
            {
              // labels have changed somehow; unable to reconstruct trace
              break;
            }

            reconstructedTrace = new List<Block>();
            reconstructedTrace.Add(implEntryBlock);
            prevBlock = implEntryBlock;
          }
          else if (prevBlock.TransferCmd is GotoCmd)
          {
            var gto = (GotoCmd)prevBlock.TransferCmd;
            Block nb = null;
            Contract.Assert(gto.labelNames.Count ==
                            gto.labelTargets
                              .Count); // follows from GotoCmd invariant and the fact that resolution should have made both lists non-null
            for (int i = 0; i < gto.labelNames.Count; i++)
            {
              if (gto.labelNames[i] == blk.Label)
              {
                nb = gto.labelTargets[i];
                break;
              }
            }

            if (nb == null)
            {
              // labels have changed somehow; unable to reconstruct trace
              reconstructedTrace = null;
              break;
            }

            reconstructedTrace.Add(nb);
            prevBlock = nb;
          }
          else
          {
            // old trace is longer somehow; unable to reconstruct trace
            reconstructedTrace = null;
            break;
          }
        }

        ReturnCmd returnCmd = null;
        if (reconstructedTrace != null)
        {
          // The reconstructed trace ends with a "return;" in the passive command, so we now try to convert it to the original (non-passive) "return;"
          foreach (Block b in reconstructedTrace)
          {
            Contract.Assert(b != null);
            Contract.Assume(b.TransferCmd != null);
            returnCmd = gotoCmdOrigins.ContainsKey(b.TransferCmd) ? gotoCmdOrigins[b.TransferCmd] : null;
            if (returnCmd != null)
            {
              break;
            }
          }

          if (returnCmd == null)
          {
            // As one last recourse, take the transfer command of the last block in the trace, if any
            returnCmd = reconstructedTrace.Last().TransferCmd as ReturnCmd;
          }
        }

        cc = new ReturnCounterexample(options, reconstructedTrace ?? cex.Trace, cex.AugmentedTrace, aa,
          returnCmd ?? oldCex.FailingReturn,
          cex.Model, cex.MvInfo, cex.Context, cex.ProofRun, aa.Checksum);
      }
      else
      {
        cc = new AssertCounterexample(options, cex.Trace, cex.AugmentedTrace, assrt, cex.Model, cex.MvInfo, cex.Context,
          cex.ProofRun);
      }

      return cc;
    }

    /*
     *
     * Encoding control flow in VC generation:
     *
     * A function ControlFlow is declared globally and used in each verification condition.
     * The function ControlFlow has two arguments:
     * (0) The first argument is a placeholder that is fixed to the constant 0 in all applications
     * of VC generation except in stratified inlining which uses different numbers to distinguish
     * different copies of the VC for different inlining contexts.
     * (1) The second argument is a unique identifier for any Absy; the VC generation only uses identifiers
     * corresponding to blocks and assert commands.
     *
     * Passification is done normally.
     *
     * While generating the equations for a block, ControlFlow pops up in two places:
     * (0) For each block A, we generate Correct_A = wlp(A, /\_{B in succ(A)} ControlFlow(0, Id(A)) == Id(B) ==> Correct_B)
     * (1) While translating block A, we have wlp(assert E, Phi) = (f(A) == Id(assert E) ==> E) && Phi
     *
     * In the description above, I am only explaining one of the options for translating assert statements.
     *
     */

    VCExpr LetVC(List<Block> blocks,
      VCExpr controlFlowVariableExpr,
      ControlFlowIdMap<Absy> absyIds,
      ProverContext proverCtxt,
      out int assertionCount,
      bool isPositiveContext = true)
    {
      Contract.Requires(blocks != null);
      Contract.Requires(proverCtxt != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      assertionCount = 0;

      Graph<Block> dag = Program.GraphFromBlocks(blocks, false);

      IEnumerable sortedNodes = dag.TopologicalSort();
      Contract.Assert(sortedNodes != null);

      Dictionary<Block, VCExprVar> blockVariables = new Dictionary<Block, VCExprVar>();
      List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      foreach (Block block in sortedNodes)
      {
        VCExpr SuccCorrect;
        GotoCmd gotocmd = block.TransferCmd as GotoCmd;
        if (gotocmd == null)
        {
          ReturnExprCmd re = block.TransferCmd as ReturnExprCmd;
          if (re == null)
          {
            SuccCorrect = VCExpressionGenerator.True;
          }
          else
          {
            SuccCorrect = proverCtxt.BoogieExprTranslator.Translate(re.Expr);
            if (isPositiveContext)
            {
              SuccCorrect = gen.Not(SuccCorrect);
            }
          }
        }
        else
        {
          Contract.Assert(gotocmd.labelTargets != null);
          List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Count);
          foreach (Block successor in gotocmd.labelTargets)
          {
            Contract.Assert(successor != null);
            VCExpr s = blockVariables[successor];
            if (controlFlowVariableExpr != null)
            {
              VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(controlFlowVariableExpr,
                gen.Integer(BigNum.FromInt(absyIds.GetId(block))));
              VCExpr controlTransferExpr =
                gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(absyIds.GetId(successor))));
              s = gen.Implies(controlTransferExpr, s);
            }

            SuccCorrectVars.Add(s);
          }

          SuccCorrect = gen.NAry(VCExpressionGenerator.AndOp, SuccCorrectVars);
        }

        VCContext context = new VCContext(Options, absyIds, proverCtxt, controlFlowVariableExpr, isPositiveContext);
        VCExpr vc = Wlp.Block(block, SuccCorrect, context);
        assertionCount += context.AssertionCount;

        VCExprVar v = gen.Variable(block.Label + "_correct", Bpl.Type.Bool);
        bindings.Add(gen.LetBinding(v, vc));
        blockVariables.Add(block, v);
      }

      return proverCtxt.ExprGen.Let(bindings, blockVariables[blocks[0]]);
    }

    VCExpr DagVC(Block block,
      VCExpr controlFlowVariableExpr,
      ControlFlowIdMap<Absy> absyIds,
      Dictionary<Block, VCExpr> blockEquations,
      ProverContext proverCtxt,
      out int assertionCount)
    {
      Contract.Requires(block != null);
      Contract.Requires(absyIds != null);
      Contract.Requires(blockEquations != null);
      Contract.Requires(proverCtxt != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      assertionCount = 0;
      VCExpressionGenerator gen = proverCtxt.ExprGen;
      Contract.Assert(gen != null);
      VCExpr vc = blockEquations[block];
      if (vc != null)
      {
        return vc;
      }

      /*
       * For block A (= block), generate:
       *   wp(A_body, (/\ S \in Successors(A) :: DagVC(S)))
       */
      VCExpr SuccCorrect = null;
      GotoCmd gotocmd = block.TransferCmd as GotoCmd;
      if (gotocmd != null)
      {
        foreach (Block successor in cce.NonNull(gotocmd.labelTargets))
        {
          Contract.Assert(successor != null);
          VCExpr c = DagVC(successor, controlFlowVariableExpr, absyIds, blockEquations, proverCtxt, out var ac);
          assertionCount += ac;
          if (controlFlowVariableExpr != null)
          {
            VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(controlFlowVariableExpr,
              gen.Integer(BigNum.FromInt(absyIds.GetId(block))));
            VCExpr controlTransferExpr =
              gen.Eq(controlFlowFunctionAppl, gen.Integer(BigNum.FromInt(absyIds.GetId(successor))));
            c = gen.Implies(controlTransferExpr, c);
          }

          SuccCorrect = SuccCorrect == null ? c : gen.And(SuccCorrect, c);
        }
      }

      if (SuccCorrect == null)
      {
        SuccCorrect = VCExpressionGenerator.True;
      }

      VCContext context = new VCContext(Options, absyIds, proverCtxt, controlFlowVariableExpr);
      vc = Wlp.Block(block, SuccCorrect, context);
      assertionCount += context.AssertionCount;

      //  gen.MarkAsSharedFormula(vc);  PR: don't know yet what to do with this guy

      blockEquations.Add(block, vc);
      return vc;
    }

    /// <summary>
    /// Remove empty blocks reachable from the startBlock of the CFG
    /// </summary>
    static void RemoveEmptyBlocks(List<Block> blocks)
    {
      // postorder traversal of cfg
      //   noting loop heads in [keep] and
      //   generating token information in [renameInfo]
      Block startBlock = blocks[0];
      var postorder = new List<Block>();
      var keep = new HashSet<Block>();
      var visited = new HashSet<Block>();
      var grey = new HashSet<Block>();
      var stack = new Stack<Block>();
      Dictionary<Block, Block> renameInfo = new Dictionary<Block, Block>();

      stack.Push(startBlock);
      visited.Add(startBlock);
      while (stack.Count != 0)
      {
        var curr = stack.Pop();
        if (grey.Contains(curr))
        {
          postorder.Add(curr);

          // generate renameInfoForStartBlock
          GotoCmd gtc = curr.TransferCmd as GotoCmd;
          renameInfo[curr] = null;
          if (gtc == null || gtc.labelTargets == null || gtc.labelTargets.Count == 0)
          {
            if (curr.Cmds.Count == 0 && curr.tok.IsValid)
            {
              renameInfo[curr] = curr;
            }
          }
          else
          {
            if (curr.Cmds.Count == 0 || curr == startBlock)
            {
              if (curr.tok.IsValid)
              {
                renameInfo[curr] = curr;
              }
              else
              {
                HashSet<Block> successorRenameInfo = new HashSet<Block>();
                foreach (Block s in gtc.labelTargets)
                {
                  if (keep.Contains(s))
                  {
                    successorRenameInfo.Add(null);
                  }
                  else
                  {
                    successorRenameInfo.Add(renameInfo[s]);
                  }
                }

                if (successorRenameInfo.Count == 1)
                {
                  renameInfo[curr] = successorRenameInfo.Single();
                }
              }
            }
          }

          // end generate renameInfoForStartBlock
        }
        else
        {
          grey.Add(curr);
          stack.Push(curr);
          GotoCmd gtc = curr.TransferCmd as GotoCmd;
          if (gtc == null || gtc.labelTargets == null || gtc.labelTargets.Count == 0)
          {
            continue;
          }

          foreach (Block s in gtc.labelTargets)
          {
            if (!visited.Contains(s))
            {
              visited.Add(s);
              stack.Push(s);
            }
            else if (grey.Contains(s) && !postorder.Contains(s))
            {
              // s is a loop head
              keep.Add(s);
            }
          }
        }
      }

      keep.Add(startBlock);

      foreach (Block b in postorder)
      {
        if (!keep.Contains(b) && b.Cmds.Count == 0)
        {
          GotoCmd bGtc = b.TransferCmd as GotoCmd;
          foreach (Block p in b.Predecessors)
          {
            GotoCmd pGtc = p.TransferCmd as GotoCmd;
            Contract.Assert(pGtc != null);
            pGtc.labelTargets.Remove(b);
            pGtc.labelNames.Remove(b.Label);
          }

          if (bGtc == null || bGtc.labelTargets == null || bGtc.labelTargets.Count == 0)
          {
            continue;
          }

          List<Block> successors = bGtc.labelTargets;

          // Try to push token information if possible
          if (b.tok.IsValid && successors.Count == 1 && b != renameInfo[startBlock])
          {
            var s = successors.Single();
            if (!s.tok.IsValid)
            {
              foreach (Block p in s.Predecessors)
              {
                if (p != b)
                {
                  GotoCmd pGtc = p.TransferCmd as GotoCmd;
                  Contract.Assert(pGtc != null);
                  pGtc.labelTargets.Remove(s);
                  pGtc.labelNames.Remove(s.Label);
                  pGtc.labelTargets.Add(s);
                  pGtc.labelNames.Add(b.Label);
                }
              }

              s.tok = b.tok;
              s.Label = b.Label;
            }
          }

          foreach (Block p in b.Predecessors)
          {
            GotoCmd pGtc = p.TransferCmd as GotoCmd;
            Contract.Assert(pGtc != null);
            foreach (Block s in successors)
            {
              if (!pGtc.labelTargets.Contains(s))
              {
                pGtc.labelTargets.Add(s);
                pGtc.labelNames.Add(s.Label);
              }
            }
          }
        }
      }

      if (!startBlock.tok.IsValid && startBlock.Cmds.All(c => c is AssumeCmd))
      {
        if (renameInfo[startBlock] != null)
        {
          startBlock.tok = renameInfo[startBlock].tok;
          startBlock.Label = renameInfo[startBlock].Label;
        }
      }
    }
  }
}