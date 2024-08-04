using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Boogie.VCExprAST;

namespace VC;

public class SmokeTester
{
  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(parent != null);
    Contract.Invariant(run != null);
    Contract.Invariant(initial != null);
    Contract.Invariant(Cce.NonNullDictionaryAndValues(copies));
    Contract.Invariant(Cce.NonNull(visited));
    Contract.Invariant(callback != null);
  }

  VerificationConditionGenerator parent;
  ImplementationRun run;
  Block initial;
  int id;
  Dictionary<Block, Block> copies = new Dictionary<Block, Block>();
  HashSet<Block> visited = new HashSet<Block>();
  VerifierCallback callback;

  internal SmokeTester(VerificationConditionGenerator par, ImplementationRun run, VerifierCallback callback)
  {
    Contract.Requires(par != null);
    Contract.Requires(run != null);
    Contract.Requires(callback != null);
    parent = par;
    this.run = run;
    initial = run.Implementation.Blocks[0];
    this.callback = callback;
  }

  private VCGenOptions Options => parent.Options;

  internal void Copy()
  {
    CloneBlock(run.Implementation.Blocks[0]);
    initial = GetCopiedBlocks()[0];
  }

  internal Task Test(TextWriter traceWriter)
  {
    Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

    return DepthFirstSearch(traceWriter, initial);
  }

  void TopologicalSortImpl()
  {
    Graph<Block> dag = Program.GraphFromImpl(run.Implementation);
    run.Implementation.Blocks = new List<Block>();
    foreach (Block b in dag.TopologicalSort())
    {
      Contract.Assert(b != null);
      run.Implementation.Blocks.Add(b);
    }
  }

  void Emit()
  {
    TopologicalSortImpl();
    ConditionGeneration.EmitImpl(Options, run, false);
  }

  // this one copies forward
  Block CloneBlock(Block b)
  {
    Contract.Requires(b != null);
    Contract.Ensures(Contract.Result<Block>() != null);

    if (copies.TryGetValue(b, out var fake_res))
    {
      return Cce.NonNull(fake_res);
    }

    Block res = new Block(b.tok, b.Label, new List<Cmd>(b.Cmds), null);
    copies[b] = res;
    if (b.TransferCmd is GotoCmd)
    {
      foreach (Block ch in Cce.NonNull((GotoCmd) b.TransferCmd).labelTargets)
      {
        Contract.Assert(ch != null);
        CloneBlock(ch);
      }
    }

    foreach (Block p in b.Predecessors)
    {
      Contract.Assert(p != null);
      res.Predecessors.Add(CloneBlock(p));
    }

    return res;
  }

  // this one copies backwards
  Block CopyBlock(Block b)
  {
    Contract.Requires(b != null);
    Contract.Ensures(Contract.Result<Block>() != null);

    if (copies.TryGetValue(b, out var fake_res))
    {
      // fake_res should be Block! but the compiler fails
      return Cce.NonNull(fake_res);
    }

    Block res;
    List<Cmd> seq = new List<Cmd>();
    foreach (Cmd c in b.Cmds)
    {
      Contract.Assert(c != null);
      AssertCmd turn = c as AssertCmd;
      if (!turnAssertIntoAssumes || turn == null)
      {
        seq.Add(c);
      }
      else
      {
        seq.Add(VerificationConditionGenerator.AssertTurnedIntoAssume(Options, turn));
      }
    }

    res = new Block(b.tok, b.Label, seq, null);
    copies[b] = res;
    foreach (Block p in b.Predecessors)
    {
      Contract.Assert(p != null);
      res.Predecessors.Add(CopyBlock(p));
    }

    return res;
  }

  List<Block> GetCopiedBlocks()
  {
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Block>>()));

    // the order of nodes in res is random (except for the first one, being the entry)
    List<Block> res = new List<Block>();
    res.Add(copies[initial]);

    foreach (KeyValuePair<Block, Block> kv in copies)
    {
      Contract.Assert(kv.Key != null && kv.Value != null);
      GotoCmd go = kv.Key.TransferCmd as GotoCmd;
      ReturnCmd ret = kv.Key.TransferCmd as ReturnCmd;
      if (kv.Key != initial)
      {
        res.Add(kv.Value);
      }

      if (go != null)
      {
        GotoCmd copy = new GotoCmd(go.tok, new List<String>(), new List<Block>());
        kv.Value.TransferCmd = copy;
        foreach (Block b in Cce.NonNull(go.labelTargets))
        {
          Contract.Assert(b != null);
          if (copies.TryGetValue(b, out var c))
          {
            copy.AddTarget(Cce.NonNull(c));
          }
        }
      }
      else if (ret != null)
      {
        kv.Value.TransferCmd = ret;
      }
      else
      {
        Contract.Assume(false);
        throw new Cce.UnreachableException();
      }
    }

    copies.Clear();

    return res;
  }

  // check if e is true, false, !true, !false
  // if so return true and the value of the expression in val
  bool BooleanEval(Expr e, ref bool val)
  {
    Contract.Requires(e != null);
    LiteralExpr lit = e as LiteralExpr;
    NAryExpr call = e as NAryExpr;

    if (lit != null && lit.isBool)
    {
      val = lit.asBool;
      return true;
    }
    else if (call != null &&
             call.Fun is UnaryOperator &&
             ((UnaryOperator) call.Fun).Op == UnaryOperator.Opcode.Not &&
             BooleanEval(Cce.NonNull(call.Args[0]), ref val))
    {
      val = !val;
      return true;
    }
    // this is for the 0bv32 != 0bv32 generated by vcc
    else if (call != null &&
             call.Fun is BinaryOperator &&
             ((BinaryOperator) call.Fun).Op == BinaryOperator.Opcode.Neq &&
             call.Args[0] is LiteralExpr &&
             Cce.NonNull(call.Args[0]).Equals(call.Args[1]))
    {
      val = false;
      return true;
    }

    return false;
  }

  bool IsFalse(Expr e)
  {
    Contract.Requires(e != null);
    bool val = false;
    return BooleanEval(e, ref val) && !val;
  }

  async Task<bool> CheckUnreachable(TextWriter traceWriter, Block cur, List<Cmd> seq)
  {
    Contract.Requires(cur != null);
    Contract.Requires(seq != null);
    Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
    foreach (Cmd cmd in seq)
    {
      AssertCmd assrt = cmd as AssertCmd;
      if (assrt != null && QKeyValue.FindBoolAttribute(assrt.Attributes, "PossiblyUnreachable"))
      {
        return false;
      }
    }

    DateTime start = DateTime.UtcNow;
    if (Options.Trace)
    {
      traceWriter.Write("    soundness smoke test #{0} ... ", id);
    }

    callback.OnProgress?.Invoke("smoke", id, id, 0.0);

    Token tok = new Token();
    tok.val = "soundness smoke test assertion";
    seq.Add(new AssertCmd(tok, Expr.False));
    Block copy = CopyBlock(cur);
    Contract.Assert(copy != null);
    copy.Cmds = seq;
    List<Block> backup = run.Implementation.Blocks;
    Contract.Assert(backup != null);
    run.Implementation.Blocks = GetCopiedBlocks();
    copy.TransferCmd = new ReturnCmd(Token.NoToken);
    if (Options.TraceVerify)
    {
      traceWriter.WriteLine();
      traceWriter.WriteLine(" --- smoke #{0}, before passify", id);
      Emit();
    }

    parent.CurrentLocalVariables = run.Implementation.LocVars;
    parent.PassifyImpl(run, out var mvInfo);
    Checker checker = await parent.CheckerPool.FindCheckerFor(parent.program, null, CancellationToken.None);
    Contract.Assert(checker != null);

    SolverOutcome outcome = SolverOutcome.Undetermined;
    var resourceCount = 0;
    try
    {
      VCExpr vc;
      var absyIds = new ControlFlowIdMap<Absy>();
      lock (checker)
      {
        var exprGen = checker.TheoremProver.Context.ExprGen;
        VCExpr controlFlowVariableExpr = exprGen.Integer(BigNum.ZERO);

        vc = parent.GenerateVC(run.Implementation, controlFlowVariableExpr, absyIds, checker.TheoremProver.Context);
        Contract.Assert(vc != null);

        VCExpr controlFlowFunctionAppl =
          exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
        VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl,
          exprGen.Integer(BigNum.FromInt(absyIds.GetId(run.Implementation.Blocks[0]))));
        vc = exprGen.Implies(eqExpr, vc);

        run.Implementation.Blocks = backup;

        if (Options.TraceVerify)
        {
          traceWriter.WriteLine(" --- smoke #{0}, after passify", id);
          Emit();
        }
      }
      await checker.BeginCheck(Cce.NonNull(Implementation.Name + "_smoke" + id++), vc, new ErrorHandler(Options, absyIds, callback),
        Options.SmokeTimeout, Options.ResourceLimit, CancellationToken.None);

      await checker.ProverTask;
      resourceCount = checker.GetProverResourceCount();

      lock (checker)
      {
        outcome = checker.ReadOutcome();
      }
    }
    finally
    {
      await checker.GoBackToIdle();
    }

    parent.CurrentLocalVariables = null;

    DateTime end = DateTime.UtcNow;
    TimeSpan elapsed = end - start;
    if (Options.Trace)
    {
      traceWriter.WriteLine("  [{0} s, resource count: {1}] {2}",
        elapsed.TotalSeconds,
        resourceCount,
        outcome == SolverOutcome.Valid
          ? "OOPS"
          : "OK" + (outcome == SolverOutcome.Invalid ? "" : " (" + outcome + ")"));
    }

    if (outcome == SolverOutcome.Valid)
    {
      // copy it again, so we get the version with calls, assignments and such
      copy = CopyBlock(cur);
      copy.Cmds = seq;
      Implementation.Blocks = GetCopiedBlocks();
      TopologicalSortImpl();
      callback.OnUnreachableCode(run);
      Implementation.Blocks = backup;
      return true;
    }

    return false;
  }

  private Implementation Implementation => run.Implementation;

  const bool turnAssertIntoAssumes = false;

  async Task DepthFirstSearch(TextWriter traceWriter, Block cur)
  {
    Contract.Requires(cur != null);
    Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
    if (visited.Contains(cur))
    {
      return;
    }

    visited.Add(cur);

    List<Cmd> seq = new List<Cmd>();
    foreach (Cmd cmd_ in cur.Cmds)
    {
      Cmd cmd = cmd_;
      Contract.Assert(cmd != null);
      AssertCmd assrt = cmd as AssertCmd;
      AssumeCmd assm = cmd as AssumeCmd;
      CallCmd call = cmd as CallCmd;

      bool assumeFalse = false;

      if (assrt != null)
      {
        // we're not going any further
        // it's clear the user expected unreachable code here
        // it's not clear where did he expect it, maybe it would be right to insert
        // a check just one command before
        if (IsFalse(assrt.Expr))
        {
          return;
        }

#if TURN_ASSERT_INFO_ASSUMES
            if (turnAssertIntoAssumes) {
              cmd = AssertTurnedIntoAssume(assrt);
            }
#endif
      }
      else if (assm != null)
      {
        if (IsFalse(assm.Expr))
        {
          assumeFalse = true;
        }
      }
      else if (call != null)
      {
        foreach (Ensures e in (Cce.NonNull(call.Proc)).Ensures)
        {
          Contract.Assert(e != null);
          if (IsFalse(e.Condition))
          {
            assumeFalse = true;
          }
        }
      }

      if (assumeFalse)
      {
        await CheckUnreachable(traceWriter, cur, seq);
        return;
      }

      seq.Add(cmd);
    }


    GotoCmd go = cur.TransferCmd as GotoCmd;
    ReturnCmd ret = cur.TransferCmd as ReturnCmd;

    Contract.Assume(!(go != null && go.labelTargets == null && go.labelNames != null && go.labelNames.Count > 0));

    if (ret != null || (go != null && Cce.NonNull(go.labelTargets).Count == 0))
    {
      // we end in return, so there will be no more places to check
      await CheckUnreachable(traceWriter, cur, seq);
    }
    else if (go != null)
    {
      bool needToCheck = true;
      // if all of our children have more than one parent, then
      // we're in the right place to check
      foreach (Block target in Cce.NonNull(go.labelTargets))
      {
        Contract.Assert(target != null);
        if (target.Predecessors.Count == 1)
        {
          needToCheck = false;
        }
      }

      if (needToCheck)
      {
        await CheckUnreachable(traceWriter, cur, seq);
      }

      foreach (Block target in go.labelTargets)
      {
        Contract.Assert(target != null);
        await DepthFirstSearch(traceWriter, target);
      }
    }
  }

  class ErrorHandler : ProverInterface.ErrorHandler
  {
    ControlFlowIdMap<Absy> absyIds;
    VerifierCallback callback;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(absyIds != null);
      Contract.Invariant(callback != null);
    }


    public ErrorHandler(VCGenOptions options, ControlFlowIdMap<Absy> absyIds, VerifierCallback callback)  : base(options)
    {
      Contract.Requires(absyIds != null);
      Contract.Requires(callback != null);
      this.absyIds = absyIds;
      this.callback = callback;
    }

    public override Absy Label2Absy(string label)
    {
      //Contract.Requires(label != null);
      Contract.Ensures(Contract.Result<Absy>() != null);

      int id = int.Parse(label);
      return Cce.NonNull((Absy) absyIds.GetValue(id));
    }

    public override void OnProverWarning(string msg)
    {
      //Contract.Requires(msg != null);
      callback.OnWarning(options, msg);
    }
  }
}
