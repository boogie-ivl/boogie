using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie;

public class Implementation : DeclWithFormals {
  public List<Variable> LocVars;

  [Rep] public StmtList StructuredStmts;

  [field: Rep]
  public List<Block> Blocks {
    get; 
    set;
  }
  public Procedure Proc;

  // Blocks before applying passification etc.
  // Both are used only when /inline is set.
  public List<Block> OriginalBlocks;
  public List<Variable> OriginalLocVars;
    
  // Map filled in during passification to allow augmented error trace reporting
  public Dictionary<Cmd, List<object>> debugInfos = new();

  public readonly ISet<byte[]> AssertionChecksums = new HashSet<byte[]>(ChecksumComparer.Default);

  public sealed class ChecksumComparer : IEqualityComparer<byte[]>
  {
    static IEqualityComparer<byte[]> defaultComparer;

    public static IEqualityComparer<byte[]> Default
    {
      get
      {
        if (defaultComparer == null)
        {
          defaultComparer = new ChecksumComparer();
        }

        return defaultComparer;
      }
    }

    public bool Equals(byte[] x, byte[] y)
    {
      if (x == null || y == null)
      {
        return x == y;
      }
      else
      {
        return x.SequenceEqual(y);
      }
    }

    public int GetHashCode(byte[] checksum)
    {
      if (checksum == null)
      {
        throw new ArgumentNullException("checksum");
      }
      else
      {
        var result = 17;
        for (int i = 0; i < checksum.Length; i++)
        {
          result = result * 23 + checksum[i];
        }

        return result;
      }
    }
  }

  public void AddAssertionChecksum(byte[] checksum)
  {
    Contract.Requires(checksum != null);

    if (AssertionChecksums != null)
    {
      AssertionChecksums.Add(checksum);
    }
  }

  public ISet<byte[]> AssertionChecksumsInCachedSnapshot { get; set; }

  public bool IsAssertionChecksumInCachedSnapshot(byte[] checksum)
  {
    Contract.Requires(AssertionChecksumsInCachedSnapshot != null);

    return AssertionChecksumsInCachedSnapshot.Contains(checksum);
  }

  public IList<AssertCmd> RecycledFailingAssertions { get; protected set; }

  public void AddRecycledFailingAssertion(AssertCmd assertion)
  {
    if (RecycledFailingAssertions == null)
    {
      RecycledFailingAssertions = new List<AssertCmd>();
    }

    RecycledFailingAssertions.Add(assertion);
  }

  public Cmd ExplicitAssumptionAboutCachedPrecondition { get; set; }

  // Strongly connected components
  private StronglyConnectedComponents<Block /*!*/> scc;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(LocVars != null);
    Contract.Invariant(cce.NonNullElements(Blocks));
    Contract.Invariant(cce.NonNullElements(OriginalBlocks, true));
    Contract.Invariant(cce.NonNullElements(scc, true));
  }

  private bool BlockPredecessorsComputed;

  public bool StronglyConnectedComponentsComputed
  {
    get { return this.scc != null; }
  }

  public bool IsSkipVerification(CoreOptions options)
  {
    bool verify = true;
    cce.NonNull(this.Proc).CheckBooleanAttribute("verify", ref verify);
    this.CheckBooleanAttribute("verify", ref verify);
    if (!verify) {
      return true;
    }

    if (options.ProcedureInlining == CoreOptions.Inlining.Assert ||
        options.ProcedureInlining == CoreOptions.Inlining.Assume) {
      Expr inl = this.FindExprAttribute("inline");
      if (inl == null) {
        inl = this.Proc.FindExprAttribute("inline");
      }

      if (inl != null) {
        return true;
      }
    }

    if (options.StratifiedInlining > 0) {
      return !QKeyValue.FindBoolAttribute(Attributes, "entrypoint");
    }

    return false;
  }

  public string Id
  {
    get
    {
      var id = (this as ICarriesAttributes).FindStringAttribute("id");
      if (id == null)
      {
        id = Name + GetHashCode().ToString() + ":0";
      }

      return id;
    }
  }

  public int Priority
  {
    get
    {
      int priority = 0;
      CheckIntAttribute("priority", ref priority);
      if (priority <= 0)
      {
        priority = 1;
      }

      return priority;
    }
  }

  public Dictionary<string, string> GetExtraSMTOptions()
  {
    Dictionary<string, string> extraSMTOpts = new();
    for (var a = Attributes; a != null; a = a.Next) {
      var n = a.Params.Count;
      var k = a.Key;
      if (k.Equals("smt_option")) {
        if (n == 2 && a.Params[0] is string s) {
          extraSMTOpts.Add(s, a.Params[1].ToString());
        }
      }
    }

    return extraSMTOpts;
  }

  public IDictionary<byte[], object> ErrorChecksumToCachedError { get; private set; }

  public bool IsErrorChecksumInCachedSnapshot(byte[] checksum)
  {
    Contract.Requires(ErrorChecksumToCachedError != null);

    return ErrorChecksumToCachedError.ContainsKey(checksum);
  }

  public void SetErrorChecksumToCachedError(IEnumerable<Tuple<byte[], byte[], object>> errors)
  {
    Contract.Requires(errors != null);

    ErrorChecksumToCachedError = new Dictionary<byte[], object>(ChecksumComparer.Default);
    foreach (var kv in errors)
    {
      ErrorChecksumToCachedError[kv.Item1] = kv.Item3;
      if (kv.Item2 != null)
      {
        ErrorChecksumToCachedError[kv.Item2] = null;
      }
    }
  }

  public bool HasCachedSnapshot
  {
    get { return ErrorChecksumToCachedError != null && AssertionChecksumsInCachedSnapshot != null; }
  }

  public bool AnyErrorsInCachedSnapshot
  {
    get
    {
      Contract.Requires(ErrorChecksumToCachedError != null);

      return ErrorChecksumToCachedError.Any();
    }
  }

  IList<LocalVariable> injectedAssumptionVariables;

  public IList<LocalVariable> InjectedAssumptionVariables
  {
    get { return injectedAssumptionVariables != null ? injectedAssumptionVariables : new List<LocalVariable>(); }
  }

  IList<LocalVariable> doomedInjectedAssumptionVariables;

  public IList<LocalVariable> DoomedInjectedAssumptionVariables
  {
    get
    {
      return doomedInjectedAssumptionVariables != null
        ? doomedInjectedAssumptionVariables
        : new List<LocalVariable>();
    }
  }

  public List<LocalVariable> RelevantInjectedAssumptionVariables(Dictionary<Variable, Expr> incarnationMap)
  {
    return InjectedAssumptionVariables.Where(v =>
    {
      if (incarnationMap.TryGetValue(v, out var e))
      {
        var le = e as LiteralExpr;
        return le == null || !le.IsTrue;
      }
      else
      {
        return false;
      }
    }).ToList();
  }

  public List<LocalVariable> RelevantDoomedInjectedAssumptionVariables(Dictionary<Variable, Expr> incarnationMap)
  {
    return DoomedInjectedAssumptionVariables.Where(v =>
    {
      if (incarnationMap.TryGetValue(v, out var e))
      {
        var le = e as LiteralExpr;
        return le == null || !le.IsTrue;
      }
      else
      {
        return false;
      }
    }).ToList();
  }

  public Expr ConjunctionOfInjectedAssumptionVariables(Dictionary<Variable, Expr> incarnationMap, out bool isTrue)
  {
    Contract.Requires(incarnationMap != null);

    var vars = RelevantInjectedAssumptionVariables(incarnationMap).Select(v => incarnationMap[v]).ToList();
    isTrue = vars.Count == 0;
    return LiteralExpr.BinaryTreeAnd(vars);
  }

  public void InjectAssumptionVariable(LocalVariable variable, bool isDoomed = false)
  {
    LocVars.Add(variable);
    if (isDoomed)
    {
      if (doomedInjectedAssumptionVariables == null)
      {
        doomedInjectedAssumptionVariables = new List<LocalVariable>();
      }

      doomedInjectedAssumptionVariables.Add(variable);
    }
    else
    {
      if (injectedAssumptionVariables == null)
      {
        injectedAssumptionVariables = new List<LocalVariable>();
      }

      injectedAssumptionVariables.Add(variable);
    }
  }

  public Implementation(IToken tok, string name, List<TypeVariable> typeParams, List<Variable> inParams,
    List<Variable> outParams, List<Variable> localVariables, [Captured] StmtList structuredStmts, QKeyValue kv)
    : this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, kv, new Errors())
  {
    Contract.Requires(structuredStmts != null);
    Contract.Requires(localVariables != null);
    Contract.Requires(outParams != null);
    Contract.Requires(inParams != null);
    Contract.Requires(typeParams != null);
    Contract.Requires(name != null);
    Contract.Requires(tok != null);
    //:this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, new Errors());
  }

  public Implementation(IToken tok, string name, List<TypeVariable> typeParams, List<Variable> inParams,
    List<Variable> outParams, List<Variable> localVariables, [Captured] StmtList structuredStmts)
    : this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, new Errors())
  {
    Contract.Requires(structuredStmts != null);
    Contract.Requires(localVariables != null);
    Contract.Requires(outParams != null);
    Contract.Requires(inParams != null);
    Contract.Requires(typeParams != null);
    Contract.Requires(name != null);
    Contract.Requires(tok != null);
    //:this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, new Errors());
  }

  public Implementation(IToken tok, string name, List<TypeVariable> typeParams, List<Variable> inParams,
    List<Variable> outParams, List<Variable> localVariables, [Captured] StmtList structuredStmts, Errors errorHandler)
    : this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, errorHandler)
  {
    Contract.Requires(errorHandler != null);
    Contract.Requires(structuredStmts != null);
    Contract.Requires(localVariables != null);
    Contract.Requires(outParams != null);
    Contract.Requires(inParams != null);
    Contract.Requires(typeParams != null);
    Contract.Requires(name != null);
    Contract.Requires(tok != null);
    //:this(tok, name, typeParams, inParams, outParams, localVariables, structuredStmts, null, errorHandler);
  }

  public Implementation(IToken /*!*/ tok,
    string /*!*/ name,
    List<TypeVariable> /*!*/ typeParams,
    List<Variable> /*!*/ inParams,
    List<Variable> /*!*/ outParams,
    List<Variable> /*!*/ localVariables,
    [Captured] StmtList /*!*/ structuredStmts,
    QKeyValue kv,
    Errors /*!*/ errorHandler)
    : base(tok, name, typeParams, inParams, outParams)
  {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(typeParams != null);
    Contract.Requires(inParams != null);
    Contract.Requires(outParams != null);
    Contract.Requires(localVariables != null);
    Contract.Requires(structuredStmts != null);
    Contract.Requires(errorHandler != null);
    LocVars = localVariables;
    StructuredStmts = structuredStmts;
    BigBlocksResolutionContext ctx = new BigBlocksResolutionContext(structuredStmts, errorHandler);
    Blocks = ctx.Blocks;
    BlockPredecessorsComputed = false;
    scc = null;
    Attributes = kv;
  }

  public Implementation(IToken tok, string name, List<TypeVariable> typeParams, List<Variable> inParams,
    List<Variable> outParams, List<Variable> localVariables, [Captured] List<Block /*!*/> block)
    : this(tok, name, typeParams, inParams, outParams, localVariables, block, null)
  {
    Contract.Requires(cce.NonNullElements(block));
    Contract.Requires(localVariables != null);
    Contract.Requires(outParams != null);
    Contract.Requires(inParams != null);
    Contract.Requires(typeParams != null);
    Contract.Requires(name != null);
    Contract.Requires(tok != null);
    //:this(tok, name, typeParams, inParams, outParams, localVariables, block, null);
  }

  public Implementation(IToken /*!*/ tok,
    string /*!*/ name,
    List<TypeVariable> /*!*/ typeParams,
    List<Variable> /*!*/ inParams,
    List<Variable> /*!*/ outParams,
    List<Variable> /*!*/ localVariables,
    [Captured] List<Block /*!*/> /*!*/ blocks,
    QKeyValue kv)
    : base(tok, name, typeParams, inParams, outParams)
  {
    Contract.Requires(name != null);
    Contract.Requires(inParams != null);
    Contract.Requires(outParams != null);
    Contract.Requires(localVariables != null);
    Contract.Requires(cce.NonNullElements(blocks));
    LocVars = localVariables;
    Blocks = blocks;
    BlockPredecessorsComputed = false;
    scc = null;
    Attributes = kv;
  }

  public override void Emit(TokenTextWriter stream, int level) {
    void BlocksWriters(TokenTextWriter stream) {
      if (this.StructuredStmts != null && !stream.Options.PrintInstrumented && !stream.Options.PrintInlined) {
        if (this.LocVars.Count > 0) {
          stream.WriteLine();
        }

        if (stream.Options.PrintUnstructured < 2) {
          if (stream.Options.PrintUnstructured == 1) {
            stream.WriteLine(this, level + 1, "/*** structured program:");
          }

          this.StructuredStmts.Emit(stream, level + 1);
          if (stream.Options.PrintUnstructured == 1) {
            stream.WriteLine(level + 1, "**** end structured program */");
          }
        }
      }

      if (StructuredStmts == null || 1 <= stream.Options.PrintUnstructured ||
          stream.Options.PrintInstrumented || stream.Options.PrintInlined) {
        foreach (Block b in Blocks) {
          b.Emit(stream, level + 1);
        }
      }
    }

    EmitImplementation(stream, level, BlocksWriters, showLocals: true);
  }

  public void EmitImplementation(TokenTextWriter stream, int level, IEnumerable<Block> blocks,
    bool showLocals) {
    EmitImplementation(stream, level, writer => {
      foreach (var block in blocks) {
        block.Emit(writer, level + 1);
      }
    }, showLocals);
  }

  public void EmitImplementation(TokenTextWriter stream, int level, Action<TokenTextWriter> printBlocks, bool showLocals)
  {
    stream.Write(this, level, "implementation ");
    EmitAttributes(stream);
    stream.Write(this, level, "{0}", TokenTextWriter.SanitizeIdentifier(this.Name));
    EmitSignature(stream, false);
    stream.WriteLine();

    stream.WriteLine(level, "{0}", '{');

    if (showLocals) {
      foreach (Variable /*!*/ v in this.LocVars)
      {
        Contract.Assert(v != null);
        v.Emit(stream, level + 1);
      }
    }

    printBlocks(stream);

    stream.WriteLine(level, "{0}", '}');

    stream.WriteLine();
    stream.WriteLine();
  }

  public override void Register(ResolutionContext rc)
  {
    // nothing to register
  }

  public override void Resolve(ResolutionContext rc)
  {
    if (Proc != null)
    {
      // already resolved
      return;
    }

    Proc = rc.LookUpProcedure(cce.NonNull(this.Name));
    if (Proc == null)
    {
      rc.Error(this, "implementation given for undeclared procedure: {0}", this.Name);
    }
    else if (Proc is ActionDecl actionDecl)
    {
      actionDecl.Impl = this;
    }

    int previousTypeBinderState = rc.TypeBinderState;
    try
    {
      RegisterTypeParameters(rc);

      rc.PushVarContext();
      rc.Proc = Proc;
      RegisterFormals(InParams, rc);
      RegisterFormals(OutParams, rc);
      foreach (Variable v in LocVars)
      {
        Contract.Assert(v != null);
        v.Register(rc);
        v.Resolve(rc);
      }
      rc.Proc = null;

      foreach (Variable v in LocVars)
      {
        Contract.Assert(v != null);
        v.ResolveWhere(rc);
      }

      rc.PushProcedureContext();
      foreach (Block b in Blocks)
      {
        b.Register(rc);
      }

      (this as ICarriesAttributes).ResolveAttributes(rc);
        
      rc.Proc = Proc;
      rc.StateMode = Proc.IsPure ? ResolutionContext.State.StateLess : ResolutionContext.State.Two;
      foreach (Block b in Blocks)
      {
        b.Resolve(rc);
      }
      rc.Proc = null;
      rc.StateMode = ResolutionContext.State.Single;

      rc.PopProcedureContext();
      rc.PopVarContext();

      Type.CheckBoundVariableOccurrences(TypeParameters,
        InParams.Select(Item => Item.TypedIdent.Type).ToList(),
        OutParams.Select(Item => Item.TypedIdent.Type).ToList(),
        this.tok, "implementation arguments",
        rc);
    }
    finally
    {
      rc.TypeBinderState = previousTypeBinderState;
    }

    SortTypeParams();
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    //Contract.Requires(tc != null);
    base.Typecheck(tc);

    Contract.Assume(this.Proc != null);

    if (this.TypeParameters.Count != Proc.TypeParameters.Count)
    {
      tc.Error(this, "mismatched number of type parameters in procedure implementation: {0}",
        this.Name);
    }
    else
    {
      // if the numbers of type parameters are different, it is
      // difficult to compare the argument types
      MatchFormals(this.InParams, Proc.InParams, "in", tc);
      MatchFormals(this.OutParams, Proc.OutParams, "out", tc);
    }

    var oldProc = tc.Proc;
    tc.Proc = Proc;
    tc.Impl = this;
    foreach (Variable /*!*/ v in LocVars)
    {
      Contract.Assert(v != null);
      v.Typecheck(tc);
    }
    foreach (Block b in Blocks)
    {
      b.Typecheck(tc);
    }
    Contract.Assert(tc.Proc == Proc);
    tc.Impl = null;
    tc.Proc = oldProc;

    if (Proc is ActionDecl || Proc is YieldProcedureDecl)
    {
      var graph = Program.GraphFromImpl(this);
      if (!Graph<Block>.Acyclic(graph))
      {
        if (Proc is ActionDecl)
        {
          tc.Error(this, "action implementation may not have loops");
        }
        else // Proc is YieldProcedureDecl
        {
          graph.ComputeLoops();
          if (!graph.Reducible)
          {
            tc.Error(this, "irreducible control flow graph not allowed");
          }
          else
          {
            TypecheckLoopAnnotations(tc, graph);
          }
        }
      }
    }
  }

  private void TypecheckLoopAnnotations(TypecheckingContext tc, Graph<Block> graph)
  {
    var yieldingProc = (YieldProcedureDecl)Proc;
    foreach (var header in graph.Headers)
    {
      var yieldingLayer = yieldingProc.Layer;
      var yieldCmd = (PredicateCmd)header.Cmds.FirstOrDefault(cmd =>
        cmd is PredicateCmd predCmd && predCmd.HasAttribute(CivlAttributes.YIELDS));
      if (yieldCmd == null)
      {
        yieldingLayer = int.MinValue;
      }
      else
      {
        var layers = yieldCmd.Layers;
        header.Cmds.Remove(yieldCmd);
        if (layers.Any())
        {
          if (layers.Count > 1)
          {
            tc.Error(header, "expected layer attribute to indicate the highest yielding layer of this loop");
            continue;
          }
          if (layers[0] > yieldingLayer)
          {
            tc.Error(header,
              "yielding layer of loop must not be more than the layer of enclosing procedure");
            continue;
          }
          yieldingLayer = layers[0];
        }
      }

      var yieldInvariants = header.Cmds
        .TakeWhile(cmd => cmd is CallCmd { Proc: YieldInvariantDecl }).OfType<CallCmd>()
        .ToList();
      header.Cmds.RemoveRange(0, yieldInvariants.Count);
      if (yieldInvariants.Any() && yieldCmd == null)
      {
        tc.Error(header, "expected :yields attribute on this loop");
      }
      foreach (var callCmd in yieldInvariants)
      {
        var yieldInvariant = (YieldInvariantDecl)callCmd.Proc;
        var calleeLayerNum = yieldInvariant.Layer;
        if (calleeLayerNum > yieldingLayer)
        {
          tc.Error(callCmd, $"loop must yield at layer {calleeLayerNum} of the called yield invariant");
        }
      }
      foreach (var predCmd in header.Cmds.TakeWhile(cmd => cmd is PredicateCmd).OfType<PredicateCmd>())
      {
        if (predCmd.Layers.Min() <= yieldingLayer &&
            VariableCollector.Collect(predCmd, true).OfType<GlobalVariable>().Any())
        {
          tc.Error(predCmd,
            "invariant may not access a global variable since one of its layers is a yielding layer of its loop");
        }
      }
        
      yieldingProc.YieldingLoops[header] = new YieldingLoop(yieldingLayer, yieldInvariants);
    }
  }

  void MatchFormals(List<Variable> /*!*/ implFormals, List<Variable> /*!*/ procFormals, string /*!*/ inout,
    TypecheckingContext /*!*/ tc)
  {
    Contract.Requires(implFormals != null);
    Contract.Requires(procFormals != null);
    Contract.Requires(inout != null);
    Contract.Requires(tc != null);
    if (implFormals.Count != procFormals.Count)
    {
      tc.Error(this, "mismatched number of {0}-parameters in procedure implementation: {1}",
        inout, this.Name);
    }
    else
    {
      // unify the type parameters so that types can be compared
      Contract.Assert(Proc != null);
      Contract.Assert(this.TypeParameters.Count == Proc.TypeParameters.Count);

      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst1 =
          new Dictionary<TypeVariable /*!*/, Type /*!*/>();
      IDictionary<TypeVariable /*!*/, Type /*!*/> /*!*/
        subst2 =
          new Dictionary<TypeVariable /*!*/, Type /*!*/>();

      for (int i = 0; i < this.TypeParameters.Count; ++i)
      {
        TypeVariable /*!*/
          newVar =
            new TypeVariable(Token.NoToken, Proc.TypeParameters[i].Name);
        Contract.Assert(newVar != null);
        subst1.Add(Proc.TypeParameters[i], newVar);
        subst2.Add(this.TypeParameters[i], newVar);
      }

      for (int i = 0; i < implFormals.Count; i++)
      {
        // the names of the formals are allowed to change from the proc to the impl

        // but types must be identical
        Type t = cce.NonNull((Variable) implFormals[i]).TypedIdent.Type.Substitute(subst2);
        Type u = cce.NonNull((Variable) procFormals[i]).TypedIdent.Type.Substitute(subst1);
        if (!t.Equals(u))
        {
          string /*!*/
            a = cce.NonNull((Variable) implFormals[i]).Name;
          Contract.Assert(a != null);
          string /*!*/
            b = cce.NonNull((Variable) procFormals[i]).Name;
          Contract.Assert(b != null);
          string /*!*/
            c;
          if (a == b)
          {
            c = a;
          }
          else
          {
            c = String.Format("{0} (named {1} in implementation)", b, a);
          }

          tc.Error(this, "mismatched type of {0}-parameter in implementation {1}: {2}", inout, this.Name, c);
        }
      }
    }
  }

  private Dictionary<Variable, Expr> /*?*/
    formalMap = null;

  public void ResetImplFormalMap()
  {
    this.formalMap = null;
  }

  public Dictionary<Variable, Expr> /*!*/ GetImplFormalMap(CoreOptions options)
  {
    Contract.Ensures(Contract.Result<Dictionary<Variable, Expr>>() != null);

    if (this.formalMap != null)
    {
      return this.formalMap;
    }
    else
    {
      Dictionary<Variable, Expr> /*!*/
        map = new Dictionary<Variable, Expr>(InParams.Count + OutParams.Count);

      Contract.Assume(this.Proc != null);
      Contract.Assume(InParams.Count == Proc.InParams.Count);
      for (int i = 0; i < InParams.Count; i++)
      {
        Variable /*!*/
          v = InParams[i];
        Contract.Assert(v != null);
        IdentifierExpr ie = new IdentifierExpr(v.tok, v);
        Variable /*!*/
          pv = Proc.InParams[i];
        Contract.Assert(pv != null);
        map.Add(pv, ie);
      }

      System.Diagnostics.Debug.Assert(OutParams.Count == Proc.OutParams.Count);
      for (int i = 0; i < OutParams.Count; i++)
      {
        Variable /*!*/
          v = cce.NonNull(OutParams[i]);
        IdentifierExpr ie = new IdentifierExpr(v.tok, v);
        Variable pv = cce.NonNull(Proc.OutParams[i]);
        map.Add(pv, ie);
      }

      this.formalMap = map;

      if (options.PrintWithUniqueASTIds)
      {
        options.OutputWriter.WriteLine("Implementation.GetImplFormalMap on {0}:", this.Name);
        using TokenTextWriter stream =
          new TokenTextWriter("<console>", options.OutputWriter, /*setTokens=*/false, /*pretty=*/ false, options);
        foreach (var e in map)
        {
          options.OutputWriter.Write("  ");
          cce.NonNull((Variable /*!*/) e.Key).Emit(stream, 0);
          options.OutputWriter.Write("  --> ");
          cce.NonNull((Expr) e.Value).Emit(stream);
          options.OutputWriter.WriteLine();
        }
      }

      return map;
    }
  }

  /// <summary>
  /// Return a collection of blocks that are reachable from the block passed as a parameter.
  /// The block must be defined in the current implementation
  /// </summary>
  public ICollection<Block /*!*/> GetConnectedComponents(Block startingBlock)
  {
    Contract.Requires(startingBlock != null);
    Contract.Ensures(cce.NonNullElements(Contract.Result<ICollection<Block>>(), true));
    Contract.Assert(this.Blocks.Contains(startingBlock));

    if (!this.BlockPredecessorsComputed)
    {
      ComputeStronglyConnectedComponents();
    }

#if DEBUG_PRINT
      System.Console.WriteLine("* Strongly connected components * \n{0} \n ** ", scc);
#endif

    foreach (ICollection<Block /*!*/> component in cce.NonNull(this.scc))
    {
      foreach (Block /*!*/ b in component)
      {
        Contract.Assert(b != null);
        if (b == startingBlock) // We found the compontent that owns the startingblock
        {
          return component;
        }
      }
    }

    {
      Contract.Assert(false);
      throw new cce.UnreachableException();
    } // if we are here, it means that the block is not in one of the components. This is an error.
  }

  /// <summary>
  /// Compute the strongly connected compontents of the blocks in the implementation.
  /// As a side effect, it also computes the "predecessor" relation for the block in the implementation
  /// </summary>
  public override void ComputeStronglyConnectedComponents()
  {
    if (!this.BlockPredecessorsComputed)
    {
      ComputePredecessorsForBlocks();
    }

    Adjacency<Block /*!*/> next = new Adjacency<Block /*!*/>(Successors);
    Adjacency<Block /*!*/> prev = new Adjacency<Block /*!*/>(Predecessors);

    this.scc = new StronglyConnectedComponents<Block /*!*/>(this.Blocks, next, prev);
    scc.Compute();


    foreach (Block /*!*/ block in this.Blocks)
    {
      Contract.Assert(block != null);
      block.Predecessors = new List<Block>();
    }
  }

  /// <summary>
  /// Reset the abstract stated computed before
  /// </summary>
  override public void ResetAbstractInterpretationState()
  {
    foreach (Block /*!*/ b in this.Blocks)
    {
      Contract.Assert(b != null);
      b.ResetAbstractInterpretationState();
    }
  }

  /// <summary>
  /// A private method used as delegate for the strongly connected components.
  /// It return, given a node, the set of its successors
  /// </summary>
  private IEnumerable /*<Block!>*/ /*!*/ Successors(Block node)
  {
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<IEnumerable>() != null);

    GotoCmd gotoCmd = node.TransferCmd as GotoCmd;

    if (gotoCmd != null)
    {
      // If it is a gotoCmd
      Contract.Assert(gotoCmd.labelTargets != null);

      return gotoCmd.labelTargets;
    }
    else
    {
      // otherwise must be a ReturnCmd
      Contract.Assert(node.TransferCmd is ReturnCmd);

      return new List<Block /*!*/>();
    }
  }

  /// <summary>
  /// A private method used as delegate for the strongly connected components.
  /// It return, given a node, the set of its predecessors
  /// </summary>
  private IEnumerable /*<Block!>*/ /*!*/ Predecessors(Block node)
  {
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<IEnumerable>() != null);

    Contract.Assert(this.BlockPredecessorsComputed);

    return node.Predecessors;
  }

  /// <summary>
  /// Compute the predecessor informations for the blocks
  /// </summary>
  public void ComputePredecessorsForBlocks()
  {
    var blocks = this.Blocks;
    foreach (Block b in blocks)
    {
      b.Predecessors = new List<Block>();
    }

    ComputePredecessorsForBlocks(blocks);

    this.BlockPredecessorsComputed = true;
  }

  public static void ComputePredecessorsForBlocks(List<Block> blocks)
  {
    foreach (var block in blocks) {
      if (block.TransferCmd is not GotoCmd gtc) {
        continue;
      }

      Contract.Assert(gtc.labelTargets != null);
      foreach (var /*!*/ dest in gtc.labelTargets)
      {
        Contract.Assert(dest != null);
        dest.Predecessors.Add(block);
      }
    }
  }

  public void PruneUnreachableBlocks(CoreOptions options)
  {
    var toVisit = new Stack<Block>();
    var reachableBlocks = new List<Block /*!*/>();
    var reachable = new HashSet<Block>(); // the set of elements in "reachableBlocks"

    toVisit.Push(Blocks[0]);
    while (toVisit.Count != 0)
    {
      var block = toVisit.Pop();
      if (!reachable.Add(block)) {
        continue;
      }

      reachableBlocks.Add(block);
      if (block.TransferCmd is GotoCmd gotoCmd) {
        if (options.PruneInfeasibleEdges) {
          foreach (var command in block.Cmds) {
            Contract.Assert(command != null);
            if (command is PredicateCmd { Expr: LiteralExpr { IsFalse: true } }) {
              // This statement sequence will never reach the end, because of this "assume false" or "assert false".
              // Hence, it does not reach its successors.
              block.TransferCmd = new ReturnCmd(block.TransferCmd.tok);
              goto NEXT_BLOCK;
            }
          }
        }

        // it seems that the goto statement at the end may be reached
        foreach (var next in gotoCmd.labelTargets) {
          Contract.Assume(next != null);
          toVisit.Push(next);
        }
      }

      NEXT_BLOCK:
      {
      }
    }

    this.Blocks = reachableBlocks;
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    //Contract.Requires(visitor != null);
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitImplementation(this);
  }

  public void FreshenCaptureStates()
  {
    // Assume commands with the "captureState" attribute allow model states to be
    // captured for error reporting.
    // Some program transformations, such as loop unrolling, duplicate parts of the
    // program, leading to "capture-state-assumes" being duplicated.  This leads
    // to ambiguity when getting a state from the model.
    // This method replaces the key of every "captureState" attribute with something
    // unique

    int FreshCounter = 0;
    foreach (var b in Blocks)
    {
      List<Cmd> newCmds = new List<Cmd>();
      for (int i = 0; i < b.Cmds.Count(); i++)
      {
        var a = b.Cmds[i] as AssumeCmd;
        if (a != null && (QKeyValue.FindStringAttribute(a.Attributes, "captureState") != null))
        {
          string StateName = QKeyValue.FindStringAttribute(a.Attributes, "captureState");
          newCmds.Add(new AssumeCmd(Token.NoToken, a.Expr, FreshenCaptureState(a.Attributes, FreshCounter)));
          FreshCounter++;
        }
        else
        {
          newCmds.Add(b.Cmds[i]);
        }
      }

      b.Cmds = newCmds;
    }
  }

  private QKeyValue FreshenCaptureState(QKeyValue Attributes, int FreshCounter)
  {
    // Returns attributes identical to Attributes, but:
    // - reversed (for ease of implementation; should not matter)
    // - with the value for "captureState" replaced by a fresh value
    Contract.Requires(QKeyValue.FindStringAttribute(Attributes, "captureState") != null);
    string FreshValue = QKeyValue.FindStringAttribute(Attributes, "captureState") + "$renamed$" + Name + "$" +
                        FreshCounter;

    QKeyValue result = null;
    while (Attributes != null)
    {
      if (Attributes.Key.Equals("captureState"))
      {
        result = new QKeyValue(Token.NoToken, Attributes.Key, new List<object>() {FreshValue}, result);
      }
      else
      {
        result = new QKeyValue(Token.NoToken, Attributes.Key, Attributes.Params, result);
      }

      Attributes = Attributes.Next;
    }

    return result;
  }
}