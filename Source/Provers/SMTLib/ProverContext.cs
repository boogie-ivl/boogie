using System;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie
{
  /// <summary>
  /// The methods of this class are called in the following order:
  ///   DeclareType*
  ///   (DeclareConstant DeclareFunction)*
  ///   AddAxiom*
  ///   DeclareGlobalVariable*
  /// At this time, all "attributes" are passed in as null.
  /// </summary>
  [ContractClass(typeof(ProverContextContracts))]
  public abstract class ProverContext : ICloneable
  {
    public int TimeoutDiagnosticsCount { get; set; }

    public readonly Dictionary<int, Tuple<AssertCmd, TransferCmd>> TimeoutDiagnosticIDToAssertion =
      new Dictionary<int, Tuple<AssertCmd, TransferCmd>>();

    protected virtual void ProcessDeclaration(Declaration decl)
    {
      Contract.Requires(decl != null);
    }

    public virtual void DeclareType(TypeCtorDecl t, string attributes)
    {
      Contract.Requires(t != null);
      ProcessDeclaration(t);
    }

    public virtual void DeclareConstant(Constant c, bool uniq, string attributes)
    {
      Contract.Requires(c != null);
      ProcessDeclaration(c);
    }

    public virtual void DeclareFunction(Function f, string attributes)
    {
      Contract.Requires(f != null);
      ProcessDeclaration(f);
    }

    public virtual void AddAxiom(Axiom a, string attributes)
    {
      Contract.Requires(a != null);
      ProcessDeclaration(a);
    }

    public virtual void DeclareGlobalVariable(GlobalVariable v, string attributes)
    {
      Contract.Requires(v != null);
      ProcessDeclaration(v);
    }

    public abstract void AddAxiom(VCExpr vc);
    public abstract string Lookup(VCExprVar var);
    public abstract VCExpressionGenerator ExprGen { get; }
    public abstract Boogie2VCExprTranslator BoogieExprTranslator { get; }
    public abstract VCGenerationOptions VCGenOptions { get; }
    public abstract object Clone();
    public abstract void Reset();
    public abstract void Clear();
  }

  [ContractClassFor(typeof(ProverContext))]
  public abstract class ProverContextContracts : ProverContext
  {
    public override void AddAxiom(VCExpr vc)
    {
    }

    public override void AddAxiom(Axiom a, string attributes)
    {
    }

    public override VCExpressionGenerator ExprGen
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);
        throw new NotImplementedException();
      }
    }

    public override Boogie2VCExprTranslator BoogieExprTranslator
    {
      get
      {
        Contract.Ensures(Contract.Result<Boogie2VCExprTranslator>() != null);
        throw new NotImplementedException();
      }
    }

    public override VCGenerationOptions VCGenOptions
    {
      get
      {
        Contract.Ensures(Contract.Result<VCGenerationOptions>() != null);
        throw new NotImplementedException();
      }
    }

    public override object Clone()
    {
      Contract.Ensures(Contract.Result<object>() != null);
      throw new NotImplementedException();
    }
  }

  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------------------------

  /// <summary>
  /// This ProverContext subclass is intended for use with untyped provers that do not require names
  /// to be declared before use.  It constructs its context from unique constants and given axioms.
  /// </summary>
  public class DeclFreeProverContext : ProverContext
  {
    private SMTLibOptions options;
    protected VCExpressionGenerator gen;
    protected VCGenerationOptions genOptions;
    protected Boogie2VCExprTranslator translator;

    protected List<Variable> distincts;
    protected List<VCExpr> axiomConjuncts;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(gen != null);
      Contract.Invariant(genOptions != null);
      Contract.Invariant(translator != null);
      Contract.Invariant(Cce.NonNullElements(distincts));
      Contract.Invariant(Cce.NonNullElements(axiomConjuncts));
    }

    public VCExprTranslator /*?*/
      exprTranslator;

    public DeclFreeProverContext(VCExpressionGenerator gen,
      VCGenerationOptions genOptions, SMTLibOptions options)
    {
      Contract.Requires(gen != null);
      Contract.Requires(genOptions != null);
      this.gen = gen;
      this.genOptions = genOptions;
      this.options = options;
      Boogie2VCExprTranslator t = new Boogie2VCExprTranslator(gen, genOptions);
      this.translator = t;

      distincts = new List<Variable>();
      axiomConjuncts = new List<VCExpr>();

      exprTranslator = null;
    }

    public override void Reset()
    {
      distincts = new List<Variable>();
      axiomConjuncts = new List<VCExpr>();
    }

    public override void Clear()
    {
      distincts = new List<Variable>();
      axiomConjuncts = new List<VCExpr>();
    }

    protected DeclFreeProverContext(DeclFreeProverContext ctxt)
    {
      Contract.Requires(ctxt != null);
      this.options = ctxt.options;
      this.gen = ctxt.gen;
      this.genOptions = ctxt.genOptions;
      Boogie2VCExprTranslator t = (Boogie2VCExprTranslator) ctxt.translator.Clone();
      Contract.Assert(t != null);
      this.translator = t;

      distincts = new List<Variable>(ctxt.distincts);
      axiomConjuncts = new List<VCExpr>(ctxt.axiomConjuncts);

      if (ctxt.exprTranslator == null)
      {
        exprTranslator = null;
      }
      else
      {
        exprTranslator = (VCExprTranslator) Cce.NonNull(ctxt.exprTranslator.Clone());
      }
    }

    public override object Clone()
    {
      Contract.Ensures(Contract.Result<object>() != null);

      return new DeclFreeProverContext(this);
    }

    public override void DeclareFunction(Function f, string attributes)
    {
      //Contract.Requires(f != null);
      base.ProcessDeclaration(f);
    }

    public override void DeclareConstant(Constant c, bool uniq, string attributes)
    {
      //Contract.Requires(c != null);
      base.DeclareConstant(c, uniq, attributes);

      // TODO: make separate distinct lists for names coming from different types
      // e.g., one for strings, one for ints, one for program types.
      if (uniq)
      {
        distincts.Add(c);
      }
    }

    public override void AddAxiom(Axiom ax, string attributes)
    {
      //Contract.Requires(ax != null);
      base.AddAxiom(ax, attributes);

      axiomConjuncts.Add(translator.Translate(ax.Expr));
    }

    public override void AddAxiom(VCExpr vc)
    {
      //Contract.Requires(vc != null);
      axiomConjuncts.Add(vc);
    }

    public VCExpr Axioms
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpr>() != null);
        VCExpr axioms = gen.NAry(VCExpressionGenerator.AndOp, axiomConjuncts);
        List<VCExpr> /*!>!*/
          distinctVars = new List<VCExpr>();
        foreach (Variable v in distincts)
        {
          Contract.Assert(v != null);
          distinctVars.Add(translator.LookupVariable(v));
        }

        axioms = gen.AndSimp(gen.Distinct(distinctVars), axioms);

        return axioms;
      }
    }

    public override string Lookup(VCExprVar var)
    {
      return exprTranslator.Lookup(var);
    }

    public override VCExpressionGenerator ExprGen
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);

        return gen;
      }
    }

    public override Boogie2VCExprTranslator BoogieExprTranslator
    {
      get
      {
        Contract.Ensures(Contract.Result<Boogie2VCExprTranslator>() != null);

        return translator;
      }
    }

    public override VCGenerationOptions VCGenOptions
    {
      get
      {
        Contract.Ensures(Contract.Result<VCGenerationOptions>() != null);

        return genOptions;
      }
    }
  }

  // Translator from VCExpressions to strings, which are implemented
  // by the various provers
  [ContractClass(typeof(VCExprTranslatorContracts))]
  public abstract class VCExprTranslator : ICloneable
  {
    public abstract string translate(VCExpr expr, int polarity);
    public abstract string Lookup(VCExprVar var);
    public abstract Object Clone();
  }

  [ContractClassFor(typeof(VCExprTranslator))]
  public abstract class VCExprTranslatorContracts : VCExprTranslator
  {
    public override object Clone()
    {
      Contract.Ensures(Contract.Result<object>() != null);
      throw new NotImplementedException();
    }

    public override string Lookup(VCExprVar var)
    {
      Contract.Requires(var != null);
      Contract.Ensures(Contract.Result<string>() != null);

      throw new NotImplementedException();
    }

    public override string translate(VCExpr expr, int polarity)
    {
      Contract.Requires(expr != null);

      Contract.Ensures(Contract.Result<string>() != null);

      throw new NotImplementedException();
    }
  }
}