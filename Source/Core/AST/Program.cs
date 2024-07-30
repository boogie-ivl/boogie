using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie;

public class Program : Absy
{
  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(cce.NonNullElements(this.topLevelDeclarations));
    Contract.Invariant(cce.NonNullElements(this.globalVariablesCache, true));
  }

  public Dictionary<object, List<object>> DeclarationDependencies { get; set; }

  public Program()
    : base(Token.NoToken)
  {
    this.topLevelDeclarations = new List<Declaration>();
  }

  public void Emit(TokenTextWriter stream)
  {
    Contract.Requires(stream != null);
    stream.SetToken(this);
    var functionAxioms = 
      this.Functions.Where(f => f.DefinitionAxioms.Any()).SelectMany(f => f.DefinitionAxioms);
    var constantAxioms = 
      this.Constants.Where(f => f.DefinitionAxioms.Any()).SelectMany(c => c.DefinitionAxioms);
    this.topLevelDeclarations.Except(functionAxioms.Concat(constantAxioms)).ToList().Emit(stream);
  }

  /// <summary>
  /// Returns the number of name resolution errors.
  /// </summary>
  /// <returns></returns>
  public int Resolve(CoreOptions options)
  {
    return Resolve(options, null);
  }

  public int Resolve(CoreOptions options, IErrorSink errorSink)
  {
    ResolutionContext rc = new ResolutionContext(errorSink, options);
    Resolve(rc);
    return rc.ErrorCount;
  }

  public override void Resolve(ResolutionContext rc)
  {
    Helpers.ExtraTraceInformation(rc.Options, "Starting resolution");

    foreach (var d in TopLevelDeclarations)
    {
      d.Register(rc);
    }

    ResolveTypes(rc);
      
    var prunedTopLevelDeclarations = new List<Declaration>();
    foreach (var d in TopLevelDeclarations.Where(d => !QKeyValue.FindBoolAttribute(d.Attributes, "ignore")))
    {
      // resolve all the declarations that have not been resolved yet 
      if (!(d is TypeCtorDecl || d is TypeSynonymDecl))
      {
        int e = rc.ErrorCount;
        d.Resolve(rc);
        if (rc.Options.OverlookBoogieTypeErrors && rc.ErrorCount != e && d is Implementation impl)
        {
          // ignore this implementation
          rc.Options.OutputWriter.WriteLine(
            "Warning: Ignoring implementation {0} because of translation resolution errors",
            impl.Name);
          rc.ErrorCount = e;
          continue;
        }
      }
      prunedTopLevelDeclarations.Add(d);
    }

    ClearTopLevelDeclarations();
    AddTopLevelDeclarations(prunedTopLevelDeclarations);

    foreach (var v in Variables)
    {
      v.ResolveWhere(rc);
    }
  }

  private void ResolveTypes(ResolutionContext rc)
  {
    Contract.Requires(rc != null);
    // first resolve type constructors
    foreach (var d in TopLevelDeclarations.OfType<TypeCtorDecl>())
    {
      if (!QKeyValue.FindBoolAttribute(d.Attributes, "ignore"))
      {
        d.Resolve(rc);
      }
    }

    // collect type synonym declarations
    List<TypeSynonymDecl /*!*/> /*!*/
      synonymDecls = new List<TypeSynonymDecl /*!*/>();
    foreach (var d in TopLevelDeclarations.OfType<TypeSynonymDecl>())
    {
      Contract.Assert(d != null);
      if (!QKeyValue.FindBoolAttribute(d.Attributes, "ignore"))
      {
        synonymDecls.Add(d);
      }
    }

    // then resolve the type synonyms by a simple fixed-point iteration
    TypeSynonymDecl.ResolveTypeSynonyms(synonymDecls, rc);
      
    // and finally resolve the datatype constructors
    foreach (var datatypeTypeCtorDecl in TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>())
    {
      foreach (var constructor in datatypeTypeCtorDecl.Constructors)
      {
        constructor.Resolve(rc);
      }
    }
  }

  public int Typecheck(CoreOptions options)
  {
    return this.Typecheck(options, (IErrorSink) null);
  }

  public int Typecheck(CoreOptions options, IErrorSink errorSink)
  {
    TypecheckingContext tc = new TypecheckingContext(errorSink, options);
    Typecheck(tc);
    return tc.ErrorCount;
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    //Contract.Requires(tc != null);
    Helpers.ExtraTraceInformation(tc.Options, "Starting typechecking");

    int oldErrorCount = tc.ErrorCount;
    foreach (var d in TopLevelDeclarations)
    {
      d.Typecheck(tc);
    }

    if (oldErrorCount == tc.ErrorCount)
    {
      // check whether any type proxies have remained uninstantiated
      TypeAmbiguitySeeker /*!*/
        seeker = new TypeAmbiguitySeeker(tc);
      foreach (var d in TopLevelDeclarations)
      {
        seeker.Visit(d);
      }
    }
  }

  public override Absy Clone()
  {
    var cloned = (Program) base.Clone();
    cloned.topLevelDeclarations = new List<Declaration>();
    cloned.AddTopLevelDeclarations(topLevelDeclarations);
    return cloned;
  }

  [Rep] private List<Declaration /*!*/> /*!*/ topLevelDeclarations;

  public IReadOnlyList<Declaration> TopLevelDeclarations
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Declaration>>()));
      return topLevelDeclarations.AsReadOnly();
    }

    set
    {
      Contract.Requires(value != null);
      // materialize the decls, in case there is any dependency
      // back on topLevelDeclarations
      var v = value.ToList();
      // remove null elements
      v.RemoveAll(d => (d == null));
      // now clear the decls
      ClearTopLevelDeclarations();
      // and add the values
      AddTopLevelDeclarations(v);
    }
  }

  public void AddTopLevelDeclaration(Declaration decl)
  {
    Contract.Requires(!TopLevelDeclarationsAreFrozen);
    Contract.Requires(decl != null);

    topLevelDeclarations.Add(decl);
    this.globalVariablesCache = null;
  }

  public void AddTopLevelDeclarations(IEnumerable<Declaration> decls)
  {
    Contract.Requires(!TopLevelDeclarationsAreFrozen);
    Contract.Requires(cce.NonNullElements(decls));

    topLevelDeclarations.AddRange(decls);
    this.globalVariablesCache = null;
  }

  public void RemoveTopLevelDeclaration(Declaration decl)
  {
    Contract.Requires(!TopLevelDeclarationsAreFrozen);

    topLevelDeclarations.Remove(decl);
    this.globalVariablesCache = null;
  }

  public void RemoveTopLevelDeclarations(Predicate<Declaration> match)
  {
    Contract.Requires(!TopLevelDeclarationsAreFrozen);

    topLevelDeclarations.RemoveAll(match);
    this.globalVariablesCache = null;
  }

  public void ClearTopLevelDeclarations()
  {
    Contract.Requires(!TopLevelDeclarationsAreFrozen);

    topLevelDeclarations.Clear();
    this.globalVariablesCache = null;
  }

  bool topLevelDeclarationsAreFrozen;

  public bool TopLevelDeclarationsAreFrozen
  {
    get { return topLevelDeclarationsAreFrozen; }
  }

  public void FreezeTopLevelDeclarations()
  {
    topLevelDeclarationsAreFrozen = true;
  }

  Dictionary<string, Implementation> implementationsCache;

  public IEnumerable<Implementation> Implementations
  {
    get
    {
      if (implementationsCache != null)
      {
        return implementationsCache.Values;
      }

      var result = TopLevelDeclarations.OfType<Implementation>();
      if (topLevelDeclarationsAreFrozen)
      {
        implementationsCache = result.ToDictionary(p => p.Id);
      }

      return result;
    }
  }

  public Implementation FindImplementation(string id)
  {
    Implementation result = null;
    if (implementationsCache != null && implementationsCache.TryGetValue(id, out result))
    {
      return result;
    }
    else
    {
      return Implementations.FirstOrDefault(i => i.Id == id);
    }
  }

  List<Axiom> axiomsCache;

  public IEnumerable<Axiom> Axioms
  {
    get
    {
      if (axiomsCache != null)
      {
        return axiomsCache;
      }

      var result = TopLevelDeclarations.OfType<Axiom>();
      if (topLevelDeclarationsAreFrozen)
      {
        axiomsCache = result.ToList();
      }

      return result;
    }
  }

  Dictionary<string, Procedure> proceduresCache;

  public IEnumerable<Procedure> Procedures
  {
    get
    {
      if (proceduresCache != null)
      {
        return proceduresCache.Values;
      }

      var result = TopLevelDeclarations.OfType<Procedure>();
      if (topLevelDeclarationsAreFrozen)
      {
        proceduresCache = result.ToDictionary(p => p.Name);
      }

      return result;
    }
  }

  public Procedure FindProcedure(string name)
  {
    Procedure result = null;
    if (proceduresCache != null && proceduresCache.TryGetValue(name, out result))
    {
      return result;
    }
    else
    {
      return Procedures.FirstOrDefault(p => p.Name == name);
    }
  }

  Dictionary<string, Function> functionsCache;

  public IEnumerable<Function> Functions
  {
    get
    {
      if (functionsCache != null)
      {
        return functionsCache.Values;
      }

      var result = TopLevelDeclarations.OfType<Function>();
      if (topLevelDeclarationsAreFrozen)
      {
        functionsCache = result.ToDictionary(f => f.Name);
      }

      return result;
    }
  }

  public Function FindFunction(string name)
  {
    Function result = null;
    if (functionsCache != null && functionsCache.TryGetValue(name, out result))
    {
      return result;
    }
    else
    {
      return Functions.FirstOrDefault(f => f.Name == name);
    }
  }

  public IEnumerable<Variable> Variables
  {
    get { return TopLevelDeclarations.OfType<Variable>(); }
  }

  public IEnumerable<Constant> Constants
  {
    get { return TopLevelDeclarations.OfType<Constant>(); }
  }

  private IEnumerable<GlobalVariable /*!*/> globalVariablesCache = null;

  public List<GlobalVariable /*!*/> /*!*/ GlobalVariables
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<GlobalVariable>>()));

      if (globalVariablesCache == null)
      {
        globalVariablesCache = TopLevelDeclarations.OfType<GlobalVariable>();
      }

      return new List<GlobalVariable>(globalVariablesCache);
    }
  }

  public readonly ConcurrentStack<TrackedNodeComponent> AllCoveredElements = new();

  public IEnumerable<Block> Blocks()
  {
    return Implementations.Select(Item => Item.Blocks).SelectMany(Item => Item);
  }

  public void ComputeStronglyConnectedComponents()
  {
    foreach (var d in this.TopLevelDeclarations)
    {
      d.ComputeStronglyConnectedComponents();
    }
  }

  /// <summary>
  /// Reset the abstract stated computed before
  /// </summary>
  public void ResetAbstractInterpretationState()
  {
    foreach (var d in this.TopLevelDeclarations)
    {
      d.ResetAbstractInterpretationState();
    }
  }

  public void UnrollLoops(int n, bool uc)
  {
    Contract.Requires(0 <= n);
    foreach (var impl in Implementations)
    {
      if (impl.Blocks != null && impl.Blocks.Count > 0)
      {
        cce.BeginExpose(impl);
        {
          Block start = impl.Blocks[0];
          Contract.Assume(start != null);
          Contract.Assume(cce.IsConsistent(start));
          impl.Blocks = LoopUnroll.UnrollLoops(start, n, uc);
          impl.FreshenCaptureStates();
        }
        cce.EndExpose();
      }
    }
  }




  public static Graph<Implementation> BuildCallGraph(CoreOptions options, Program program)
  {
    Graph<Implementation> callGraph = new Graph<Implementation>();
    Dictionary<Procedure, HashSet<Implementation>> procToImpls = new Dictionary<Procedure, HashSet<Implementation>>();
    foreach (var proc in program.Procedures)
    {
      procToImpls[proc] = new HashSet<Implementation>();
    }

    foreach (var impl in program.Implementations)
    {
      if (impl.IsSkipVerification(options))
      {
        continue;
      }

      callGraph.AddSource(impl);
      procToImpls[impl.Proc].Add(impl);
    }

    foreach (var impl in program.Implementations)
    {
      if (impl.IsSkipVerification(options))
      {
        continue;
      }

      foreach (Block b in impl.Blocks)
      {
        foreach (Cmd c in b.Cmds)
        {
          CallCmd cc = c as CallCmd;
          if (cc == null)
          {
            continue;
          }

          foreach (Implementation callee in procToImpls[cc.Proc])
          {
            callGraph.AddEdge(impl, callee);
          }
        }
      }
    }

    return callGraph;
  }

  public static Graph<Block> GraphFromBlocks(List<Block> blocks, bool forward = true)
  {
    Graph<Block> g = new Graph<Block>();
    void AddEdge(Block a, Block b) {
      Contract.Assert(a != null && b != null);
      if (forward) {
        g.AddEdge(a, b);
      } else {
        g.AddEdge(b, a);
      }
    }

    g.AddSource(cce.NonNull(blocks[0])); // there is always at least one node in the graph
    foreach (Block b in blocks)
    {
      if (b.TransferCmd is GotoCmd gtc)
      {
        Contract.Assume(gtc.labelTargets != null);
        gtc.labelTargets.ForEach(dest => AddEdge(b, dest));
      }
    }
    return g;
  }

  public static Graph<Block /*!*/> /*!*/ GraphFromImpl(Implementation impl, bool forward = true)
  {
    Contract.Requires(impl != null);
    Contract.Ensures(cce.NonNullElements(Contract.Result<Graph<Block>>().Nodes));
    Contract.Ensures(Contract.Result<Graph<Block>>() != null);

    return GraphFromBlocks(impl.Blocks, forward);
  }

  public class IrreducibleLoopException : Exception
  {
  }

  public Graph<Block> ProcessLoops(CoreOptions options, Implementation impl)
  {
    impl.PruneUnreachableBlocks(options);
    impl.ComputePredecessorsForBlocks();
    Graph<Block> g = GraphFromImpl(impl);
    g.ComputeLoops();
    if (g.Reducible)
    {
      return g;
    }
    throw new IrreducibleLoopException();
  }


  public override Absy StdDispatch(StandardVisitor visitor)
  {
    //Contract.Requires(visitor != null);
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitProgram(this);
  }

  int extractedFunctionCount;

  public string FreshExtractedFunctionName()
  {
    var c = System.Threading.Interlocked.Increment(ref extractedFunctionCount);
    return string.Format("##extracted_function##{0}", c);
  }

  private int invariantGenerationCounter = 0;

  public Constant MakeExistentialBoolean()
  {
    Constant ExistentialBooleanConstant = new Constant(Token.NoToken,
      new TypedIdent(tok, "_b" + invariantGenerationCounter, Microsoft.Boogie.Type.Bool), false);
    invariantGenerationCounter++;
    ExistentialBooleanConstant.AddAttribute("existential", new object[] {Expr.True});
    AddTopLevelDeclaration(ExistentialBooleanConstant);
    return ExistentialBooleanConstant;
  }

  public PredicateCmd CreateCandidateInvariant(Expr e, string tag = null)
  {
    Constant ExistentialBooleanConstant = MakeExistentialBoolean();
    IdentifierExpr ExistentialBoolean = new IdentifierExpr(Token.NoToken, ExistentialBooleanConstant);
    PredicateCmd invariant = new AssertCmd(Token.NoToken, Expr.Imp(ExistentialBoolean, e));
    if (tag != null)
    {
      invariant.Attributes = new QKeyValue(Token.NoToken, "tag", new List<object>(new object[] {tag}), null);
    }

    return invariant;
  }

  public Monomorphizer monomorphizer;
}
