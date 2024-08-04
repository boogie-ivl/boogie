using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie.SMTLib;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie;

public enum SolverOutcome
{
  Valid,
  Invalid,
  TimeOut,
  OutOfMemory,
  OutOfResource,
  Undetermined,
  Bounded
}

public abstract class ProverInterface
{
  public static ProverInterface CreateProver(SMTLibOptions libOptions, Program prog,
    string /*?*/ logFilePath, bool appendLogFile, uint timeout,
    int taskID = -1)
  {
    Contract.Requires(prog != null);

    ProverOptions options = Cce.NonNull(libOptions.TheProverFactory).BlankProverOptions(libOptions);

    if (logFilePath != null)
    {
      options.LogFilename = logFilePath;
      if (appendLogFile)
      {
        options.AppendLogFile = appendLogFile;
      }
    }

    if (timeout > 0)
    {
      options.TimeLimit = Util.BoundedMultiply(timeout, 1000);
    }

    if (taskID >= 0)
    {
      options.Parse(libOptions.Cho[taskID].ProverOptions);
    }
    else
    {
      options.Parse(libOptions.ProverOptions);
    }

    ProverContext ctx = libOptions.TheProverFactory.NewProverContext(options);

    // set up the context
    foreach (Declaration decl in prog.TopLevelDeclarations)
    {
      Contract.Assert(decl != null);
      TypeCtorDecl t = decl as TypeCtorDecl;
      if (t != null)
      {
        ctx.DeclareType(t, null);
      }
    }

    foreach (Declaration decl in prog.TopLevelDeclarations)
    {
      Contract.Assert(decl != null);
      Constant c = decl as Constant;
      if (c != null)
      {
        ctx.DeclareConstant(c, c.Unique, null);
      }
      else
      {
        Function f = decl as Function;
        if (f != null)
        {
          ctx.DeclareFunction(f, null);
        }
      }
    }

    foreach (var ax in prog.Axioms)
    {
      ctx.AddAxiom(ax, null);
    }

    foreach (Declaration decl in prog.TopLevelDeclarations)
    {
      Contract.Assert(decl != null);
      GlobalVariable v = decl as GlobalVariable;
      if (v != null)
      {
        ctx.DeclareGlobalVariable(v, null);
      }
    }

    return libOptions.TheProverFactory.SpawnProver(libOptions, options, ctx);
  }

  public readonly ISet<VCExprVar> NamedAssumes = new HashSet<VCExprVar>();

  public class ErrorHandler
  {
    protected SMTLibOptions options;

    protected ErrorHandler(SMTLibOptions options)
    {
      this.options = options;
    }

    public virtual void AddCoveredElement(TrackedNodeComponent elt)
    {
      throw new System.NotImplementedException();
    }

    // Used in CheckOutcomeCore
    public virtual int StartingProcId()
    {
      return 0;
    }

    public virtual void OnModel(IList<string> labels, Model model, SolverOutcome proverOutcome)
    {
      Contract.Requires(Cce.NonNullElements(labels));
    }

    public virtual void OnResourceExceeded(string message,
      IEnumerable<Tuple<AssertCmd, TransferCmd>> assertCmds = null)
    {
      Contract.Requires(message != null);
    }

    public virtual void OnProverWarning(string message)
    {
      Contract.Requires(message != null);
      switch (options.PrintProverWarnings)
      {
        case CoreOptions.ProverWarnings.None:
          break;
        case CoreOptions.ProverWarnings.Stdout:
          options.OutputWriter.WriteLine("Prover warning: " + message);
          break;
        case CoreOptions.ProverWarnings.Stderr:
          Console.Error.WriteLine("Prover warning: " + message);
          break;
        default:
          Contract.Assume(false);
          throw new Cce.UnreachableException(); // unexpected case
      }
    }

    public virtual void OnProverError(string message)
    {
      // no-op by default.
      //Errors are always printed to console by the prover
    }

    public virtual Absy Label2Absy(string label)
    {
      Contract.Requires(label != null);
      Contract.Ensures(Contract.Result<Absy>() != null);

      throw new System.NotImplementedException();
    }
  }

  public abstract Task<SolverOutcome> Check(string descriptiveName, VCExpr vc, ErrorHandler handler, int errorLimit, CancellationToken cancellationToken);

  public virtual void LogComment(string comment)
  {
    Contract.Requires(comment != null);
  }

  public virtual void Close()
  {
  }

  public abstract Task Reset(VCExpressionGenerator gen);

  public abstract void FullReset(VCExpressionGenerator gen);

  /// <summary>
  /// MSchaef: Allows to Push a VCExpression as Axiom on the prover stack (beta)
  /// for now it is only implemented by ProcessTheoremProver and still requires some
  /// testing
  /// </summary>
  public virtual void PushVCExpression(VCExpr vc)
  {
    Contract.Requires(vc != null);
    throw new NotImplementedException();
  }

  public virtual string VCExpressionToString(VCExpr vc)
  {
    Contract.Requires(vc != null);
    Contract.Ensures(Contract.Result<string>() != null);
    throw new NotImplementedException();
  }

  public virtual void Pop()
  {
    Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
    throw new NotImplementedException();
  }

  public virtual int NumAxiomsPushed()
  {
    throw new NotImplementedException();
  }

  public virtual int FlushAxiomsToTheoremProver()
  {
    Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
    throw new NotImplementedException();
  }

  // (assert vc)
  public virtual void Assert(VCExpr vc, bool polarity, bool isSoft = false, int weight = 1, string name = null)
  {
    throw new NotImplementedException();
  }

  public virtual Task<List<string>> UnsatCore()
  {
    throw new NotImplementedException();
  }


  // (assert implicit-axioms)
  public virtual void AssertAxioms()
  {
    throw new NotImplementedException();
  }

  // (check-sat)
  public virtual void Check()
  {
    throw new NotImplementedException();
  }

  // (check-sat + get-unsat-core + checkOutcome)
  public virtual Task<(SolverOutcome, List<int>)> CheckAssumptions(List<VCExpr> assumptions, ErrorHandler handler,
    CancellationToken cancellationToken)
  {
    throw new NotImplementedException();
  }

  public virtual Task<(SolverOutcome, List<int>)> CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions,
    ErrorHandler handler, CancellationToken cancellationToken)
  {
    throw new NotImplementedException();
  }

  // (push 1)
  public virtual void Push()
  {
    throw new NotImplementedException();
  }

  // Set theorem prover timeout for the next "check-sat"
  public virtual void SetTimeout(uint ms)
  {
  }

  public virtual void SetRlimit(uint limit)
  {
  }

  public virtual void SetAdditionalSmtOptions(IEnumerable<OptionValue> entries)
  {
  }
  
  public virtual int GetRCount()
  {
    throw new NotImplementedException();
  }

  public abstract ProverContext Context { get; }

  public abstract VCExpressionGenerator VCExprGen { get; }

  public virtual void DefineMacro(Macro fun, VCExpr vc)
  {
    throw new NotImplementedException();
  }

  public class VCExprEvaluationException : Exception
  {
  }

  public virtual Task<object> Evaluate(VCExpr expr)
  {
    throw new NotImplementedException();
  }

  // Assert vc tagged with a name
  public virtual void AssertNamed(VCExpr vc, bool polarity, string name)
  {
    throw new NotImplementedException();
  }

  public abstract Task GoBackToIdle();
}
public class UnexpectedProverOutputException : ProverException
{
  public UnexpectedProverOutputException(string s)
    : base(s)
  {
  }
}

public class ProverDiedException : UnexpectedProverOutputException
{
  public ProverDiedException()
    : base("Prover died with no further output, perhaps it ran out of memory or was killed.")
  {
  }
}
