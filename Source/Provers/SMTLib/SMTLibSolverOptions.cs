using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.SMTLib
{
  public class OptionValue
  {
    public readonly string Option;
    public readonly string Value;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Option != null);
      Contract.Invariant(Value != null);
    }

    public OptionValue(string option, string value)
    {
      Contract.Requires(option != null);
      Contract.Requires(value != null);
      Option = option;
      Value = value;
    }
  }

  public enum SolverKind
  {
    Z3,
    CVC5,
    YICES2,
    NoOpWithZ3Options,
  }

  public class SMTLibSolverOptions : ProverOptions
  {
    public bool UseWeights = true;
    public bool UseTickleBool => Solver == SolverKind.Z3;
    public SolverKind Solver = SolverKind.Z3;
    public List<OptionValue> SmtOptions = new();
    public List<string> SolverArguments = new();
    public string Logic = null;

    // Z3 specific (at the moment; some of them make sense also for other provers)
    public string Inspector = null;
    
    public SMTLibSolverOptions(SMTLibOptions libOptions) : base(libOptions)
    {
    }

    public void AddSolverArgument(string s)
    {
      SolverArguments.Add(s);
    }

    public void AddSmtOption(string name, string val)
    {
      SmtOptions.Add(new OptionValue(name, val));
    }

    public void AddWeakSmtOption(string name, string val)
    {
      if (!SmtOptions.Any(o => o.Option == name))
      {
        SmtOptions.Add(new OptionValue(name, val));
      }
    }

    public void AddSmtOption(string opt)
    {
      var idx = opt.IndexOf('=');
      if (idx <= 0 || idx == opt.Length - 1)
      {
        ReportError("Options to be passed to the prover should have the format: <name>=<value>, got '" + opt + "'");
      }

      AddSmtOption(opt.Substring(0, idx), opt.Substring(idx + 1));
    }

    protected override bool Parse(string opt)
    {
      if (opt.StartsWith("O:"))
      {
        AddSmtOption(opt.Substring(2));
        return true;
      }

      if (opt.StartsWith("C:"))
      {
        AddSolverArgument(opt.Substring(2));
        return true;
      }

      string solverStr = null;
      if (ParseString(opt, "SOLVER", ref solverStr))
      {
        switch (solverStr.ToLower())
        {
          case "noop":
            Solver = SolverKind.NoOpWithZ3Options;
            break;
          case "z3":
            Solver = SolverKind.Z3;
            break;
          case "cvc5":
            Solver = SolverKind.CVC5;
            break;
          case "yices2":
            Solver = SolverKind.YICES2;
            break;
          default:
            ReportError("Invalid SOLVER value; must be 'Z3' or 'CVC5' or 'Yices2' or 'noop'");
            return false;
        }

        return true;
      }

      return
        ParseBool(opt, "USE_WEIGHTS", ref UseWeights) ||
        ParseString(opt, "INSPECTOR", ref Inspector) ||
        ParseString(opt, "LOGIC", ref Logic) ||
        base.Parse(opt);
    }

    public override void PostParse()
    {
      base.PostParse();

      string SolverBinaryName = null;
      switch (Solver)
      {
        case SolverKind.Z3:
          Z3.SetDefaultOptions(this);
          SolverArguments.Add("-smt2 -in");
          SolverBinaryName = Solver.ToString().ToLower();
          break;
        case SolverKind.CVC5:
          SolverArguments.Add(
            "--lang=smt --no-strict-parsing --no-condense-function-values --incremental --produce-models");
          if (Logic == null)
          {
            Logic = "ALL";
          }

          SolverBinaryName = Solver.ToString().ToLower();
          break;
        case SolverKind.YICES2:
          SolverArguments.Add("--incremental");
          if (Logic == null)
          {
            Logic = "ALL";
          }

          SolverBinaryName = "yices-smt2";
          break;
        case SolverKind.NoOpWithZ3Options:
          ProverName = "noop";
          break;
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException();
      }

      if (ProverName == null) {
        ProverName = SolverBinaryName;
      }
    }

    public override string Help
    {
      get
      {
        return
          base.Help +
          @"
SMT-specific options:
~~~~~~~~~~~~~~~~~~~~~
SOLVER=<string>           Use the given SMT solver (z3, cvc5, yices2, noop;
                          default: z3). The noop solver never does any solving
                          and always returns unknown.
LOGIC=<string>            Pass (set-logic <string>) to the prover
                          (default: empty, 'ALL' for CVC5)
USE_WEIGHTS=<bool>        Pass :weight annotations on quantified formulas
                          (default: true)
VERBOSITY=<int>           1 - print prover output (default: 0)
O:<name>=<value>          Pass (set-option :<name> <value>) to the SMT solver.
C:<string>                Pass <string> to the SMT solver on the command line.

Z3-specific options:
~~~~~~~~~~~~~~~~~~~~
INSPECTOR=<string>        Use the specified Z3Inspector binary.
";
      }
    }
  }
}
