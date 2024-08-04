using System;
using System.Text;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.BaseTypes;

// A translator from Boogie AST to VCExpr AST.

namespace Microsoft.Boogie.VCExprAST
{
  using Microsoft.Boogie;

  // TODO: in future we might use that for defining symbols for Boogie's conditional compilation 
  public class VCGenerationOptions
  {
    public readonly CoreOptions Options;
    private readonly List<string> supportedProverCommands;

    public bool IsProverCommandSupported(string kind)
    {
      return supportedProverCommands.Contains(kind);
    }

    public bool IsAnyProverCommandSupported(string kinds)
    {
      if (kinds.IndexOf(',') < 0)
      {
        return IsProverCommandSupported(kinds);
      }
      else
      {
        return kinds.Split(',', ' ').Any(k => IsProverCommandSupported(k));
      }
    }

    public VCGenerationOptions(CoreOptions options, List<string> supportedProverCommands)
    {
      this.Options = options;
      this.supportedProverCommands = supportedProverCommands;
    }
  }

  public delegate VCExpr CodeExprConverter(CodeExpr codeExpr, List<VCExprLetBinding> bindings, bool isPositiveContext, Dictionary<Cmd, List<object>> debugInfos);

  public class Boogie2VCExprTranslator : ReadOnlyVisitor, ICloneable
  {
    // Stack on which the various Visit-methods put the result of the translation
    private readonly Stack<VCExpr /*!*/> /*!*/
      SubExpressions = new Stack<VCExpr>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Cce.NonNullElements(SubExpressions));
      Contract.Invariant(Gen != null);
    }


    private void Push(VCExpr expr)
    {
      Contract.Requires(expr != null);
      SubExpressions.Push(expr);
    }

    private VCExpr Pop()
    {
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return SubExpressions.Pop();
    }

    public VCExpr Translate(Expr expr)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      this.Visit(expr);
      return Pop();
    }

    public List<VCExpr /*!*/> /*!*/ Translate(IList<Expr> exprs)
    {
      Contract.Requires(exprs != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
      List<VCExpr /*!*/> /*!*/
        res = new List<VCExpr /*!*/>();
      foreach (Expr e in exprs)
      {
        res.Add(Translate(Cce.NonNull(e)));
      }

      return res;
    }

    ///////////////////////////////////////////////////////////////////////////////

    internal readonly VCExpressionGenerator /*!*/
      Gen;

    public Boogie2VCExprTranslator(VCExpressionGenerator gen,
      VCGenerationOptions genOptions)
    {
      Contract.Requires(gen != null);
      Contract.Requires(genOptions != null);
      this.Gen = gen;
      this.GenerationOptions = genOptions;
      UnboundVariables = new VariableMapping<Variable>();
      BoundVariables = new VariableMapping<BoundVariable>();
      Formals = new VariableMapping<Formal>();
    }

    private Boogie2VCExprTranslator(Boogie2VCExprTranslator tl)
    {
      Contract.Requires(tl != null);
      this.Gen = tl.Gen;
      this.GenerationOptions = tl.GenerationOptions;
      UnboundVariables =
        (VariableMapping<Variable>) tl.UnboundVariables.Clone();
      BoundVariables = new VariableMapping<BoundVariable>();
      Formals = new VariableMapping<Formal>();
    }

    public object Clone()
    {
      Contract.Ensures(Contract.Result<object>() != null);
      return new Boogie2VCExprTranslator(this);
    }

    private IAppliableTranslator IAppTranslatorAttr = null;

    private IAppliableTranslator IAppTranslator
    {
      get
      {
        Contract.Ensures(Contract.Result<IAppliableTranslator>() != null);

        if (IAppTranslatorAttr == null)
        {
          IAppTranslatorAttr = new IAppliableTranslator(this);
        }

        return IAppTranslatorAttr;
      }
    }

    ///////////////////////////////////////////////////////////////////////////////
    // Class for handling occurring variables

    private class VariableMapping<VarKind> : ICloneable
    {
      private readonly List<Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/> /*!*/
        Mapping;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Mapping != null && Contract.ForAll(Mapping, i => Cce.NonNullDictionaryAndValues(i)));
      }


      public VariableMapping()
      {
        List<Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/> /*!*/
          mapping =
            new List<Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/>();
        mapping.Add(new Dictionary<VarKind /*!*/, VCExprVar /*!*/>());
        this.Mapping = mapping;
      }

      private VariableMapping(VariableMapping<VarKind> vm)
      {
        Contract.Requires(vm != null);
        List<Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/> /*!*/
          mapping =
            new List<Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/>();
        foreach (Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/ d in vm.Mapping)
        {
          Contract.Assert(Cce.NonNullDictionaryAndValues(d));
          mapping.Add(new Dictionary<VarKind /*!*/, VCExprVar /*!*/>(d));
        }

        this.Mapping = mapping;
      }

      public object Clone()
      {
        Contract.Ensures(Contract.Result<object>() != null);
        return new VariableMapping<VarKind>(this);
      }

      public void PushScope()
      {
        Mapping.Add(new Dictionary<VarKind /*!*/, VCExprVar /*!*/>());
      }

      public void PopScope()
      {
        Contract.Assume(Mapping.Count > 0);
        Mapping.RemoveAt(Mapping.Count - 1);
      }

      public void Bind(VarKind boogieVar, VCExprVar /*!*/ vcExprVar)
      {
        Contract.Requires(vcExprVar != null);
        Contract.Requires(boogieVar != null);
        Contract.Requires(!Contains(boogieVar));
        Mapping[Mapping.Count - 1].Add(boogieVar, vcExprVar);
      }

      public VCExprVar Lookup(VarKind boogieVar)
      {
        Contract.Requires(boogieVar != null);
        Contract.Ensures(Contract.Result<VCExprVar>() != null);
        VCExprVar res = LookupHelp(boogieVar);
        Contract.Assume(res != null);
        return res;
      }

      [Pure]
      public bool Contains(VarKind boogieVar)
      {
        Contract.Requires(boogieVar != null);
        return LookupHelp(boogieVar) != null;
      }

      public bool TryGetValue(VarKind boogieVar, out VCExprVar res)
      {
        Contract.Requires(boogieVar != null);
        res = LookupHelp(boogieVar);
        return res != null;
      }

      [Pure]
      private VCExprVar LookupHelp(VarKind boogieVar)
      {
        Contract.Requires(boogieVar != null);
        foreach (Dictionary<VarKind /*!*/, VCExprVar /*!*/> /*!*/ d in Mapping)
        {
          //Contract.Assert(cce.NonNullElements(d));
          if (d.TryGetValue(boogieVar, out var res))
          {
            Contract.Assert(res != null);
            return res;
          }
        }

        return null;
      }
    }

    //////////////////////////////////////////////////////////////////////////////////

    private readonly VariableMapping<Variable> /*!*/
      UnboundVariables;

    private readonly VariableMapping<BoundVariable> /*!*/
      BoundVariables;

    // used when translating the bodies of function expansions
    private readonly VariableMapping<Formal> /*!*/
      Formals;

    [ContractInvariantMethod]
    void ObjectInvairant()
    {
      Contract.Invariant(UnboundVariables != null);
      Contract.Invariant(BoundVariables != null);
      Contract.Invariant(Formals != null);
    }


    internal void PushBoundVariableScope()
    {
      BoundVariables.PushScope();
    }

    internal void PopBoundVariableScope()
    {
      BoundVariables.PopScope();
    }

    internal void PushFormalsScope()
    {
      Formals.PushScope();
    }

    internal void PopFormalsScope()
    {
      Formals.PopScope();
    }

    public VCExprVar BindVariable(Variable boogieVar)
    {
      Contract.Requires(boogieVar != null);
      Contract.Ensures(Contract.Result<VCExprVar>() != null);
      if (boogieVar is BoundVariable)
      {
        VCExprVar /*!*/
          newVar = Gen.Variable(boogieVar.Name, boogieVar.TypedIdent.Type);
        BoundVariables.Bind((BoundVariable) boogieVar, newVar);
        return newVar;
      }
      else if (boogieVar is Formal)
      {
        VCExprVar /*!*/
          newVar = Gen.Variable(boogieVar.Name, boogieVar.TypedIdent.Type);
        Formals.Bind((Formal) boogieVar, newVar);
        return newVar;
      }
      else
      {
        // only bound variables and formals are declared explicitly
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      }
    }

    public VCExprVar LookupVariable(Variable boogieVar)
    {
      Contract.Requires(boogieVar != null);
      Contract.Ensures(Contract.Result<VCExprVar>() != null);

      BoundVariable bv = boogieVar as BoundVariable;
      if (bv != null)
      {
        return BoundVariables.Lookup(bv);
      }

      Formal fml = boogieVar as Formal;
      if (fml != null && Formals.TryGetValue(fml, out var res))
      {
        return Cce.NonNull(res);
      }

      // global variables, local variables, incarnations, etc. are
      // bound the first time they occur
      if (!UnboundVariables.TryGetValue(boogieVar, out res))
      {
        if (boogieVar is Constant)
        {
          res = new VCExprConstant(boogieVar.Name, boogieVar.TypedIdent.Type);
        }
        else
        {
          res = new VCExprVar(boogieVar.Name, boogieVar.TypedIdent.Type);
        }

        UnboundVariables.Bind(boogieVar, res);
      }

      return Cce.NonNull(res);
    }

    /// <summary>
    /// Unlike LookupVariable, this method does not create a new variable mapping if none is
    /// found.  Instead, this method returns null in such cases.  Also, this method does not
    /// look for bound variables.
    /// </summary>
    /// <param name="boogieVar"></param>
    /// <returns></returns>
    public VCExprVar TryLookupVariable(Variable boogieVar)
    {
      Contract.Requires(boogieVar != null);

      Formal fml = boogieVar as Formal;
      if (fml != null && Formals.TryGetValue(fml, out var res))
      {
        return Cce.NonNull(res);
      }

      if (UnboundVariables.TryGetValue(boogieVar, out res))
      {
        return Cce.NonNull(res);
      }

      return null; // not present
    }

    ///////////////////////////////////////////////////////////////////////////////////

    internal readonly VCGenerationOptions /*!*/
      GenerationOptions;

    [ContractInvariantMethod]
    void ObjectInvarian()
    {
      Contract.Invariant(GenerationOptions != null);
    }

    ///////////////////////////////////////////////////////////////////////////////////

    public override Expr VisitLiteralExpr(LiteralExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Push(TranslateLiteralExpr(node));
      return node;
    }

    private VCExpr TranslateLiteralExpr(LiteralExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      if (node.Val is bool)
      {
        bool b = (bool) node.Val;
        if (b)
        {
          return VCExpressionGenerator.True;
        }
        else
        {
          return VCExpressionGenerator.False;
        }
      }
      else if (node.Val is BigNum)
      {
        return Gen.Integer(node.asBigNum);
      }
      else if (node.Val is BigDec)
      {
        return Gen.Real(node.asBigDec);
      }
      else if (node.Val is BigFloat)
      {
        return Gen.Float(node.asBigFloat);
      }
      else if (node.Val is RoundingMode)
      {
        return Gen.RMode(node.asRoundingMode);
      }
      else if (node.Val is String)
      {
        return Gen.String(node.asString);
      }
      else if (node.Val is BvConst)
      {
        return Gen.Bitvector((BvConst) node.Val);
      }
      else
      {
        System.Diagnostics.Debug.Assert(false, "unknown kind of literal " + node.tok.ToString());
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      }
    }

    ///////////////////////////////////////////////////////////////////////////////////

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Contract.Assume(node.Decl != null); // the expression has to be resolved
      Push(LookupVariable(node.Decl));
      return node;
    }

    ///////////////////////////////////////////////////////////////////////////////////

    // Because of our scheme for numbering incarnations of variables, the pre-state
    // value of a variable x is always just "x". (The first update to it in a method
    // causes it to become "x0". So we just remove old expressions with a visitor
    // before transforming it into a VCExpr.
    public override Expr VisitOldExpr(OldExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    ///////////////////////////////////////////////////////////////////////////////////

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Push(TranslateNAryExpr(node));
      return node;
    }

    public bool isPositiveContext = true;

    private VCExpr TranslateNAryExpr(NAryExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      if (node.Fun is FieldUpdate fieldUpdate)
      {
        return TranslateNAryExpr(fieldUpdate.Update(Token.NoToken, node.Args[0], node.Args[1]));
      }
      
      bool flipContextForArg0 = false;
      if (node.Fun is UnaryOperator)
      {
        UnaryOperator oper = (UnaryOperator) node.Fun;
        if (oper.Op == UnaryOperator.Opcode.Not)
        {
          flipContextForArg0 = true;
        }
      }
      else if (node.Fun is BinaryOperator)
      {
        BinaryOperator oper = (BinaryOperator) node.Fun;
        if (oper.Op == BinaryOperator.Opcode.Imp)
        {
          flipContextForArg0 = true;
        }
      }

      int n = node.Args.Count;
      List<VCExpr /*!*/> /*!*/
        vcs = new List<VCExpr /*!*/>(n);

      for (int i = 0; i < n; i++)
      {
        if (i == 0 && flipContextForArg0)
        {
          isPositiveContext = !isPositiveContext;
        }

        vcs.Add(Translate(Cce.NonNull(node.Args)[i]));
        if (i == 0 && flipContextForArg0)
        {
          isPositiveContext = !isPositiveContext;
        }
      }

      if (node.Type == null)
      {
        System.Console.WriteLine("*** type is null for {0}", node);
        Contract.Assert(false);
        throw new Cce.UnreachableException();
      }

      return IAppTranslator.Translate(node.Fun, node.Type, vcs,
        ToList(Cce.NonNull(node.TypeParameters)));
    }


    private static List<Type /*!*/> /*!*/
      EMPTY_TYPE_LIST = new List<Type /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvirant()
    {
      Contract.Invariant(EMPTY_TYPE_LIST != null);
    }


    private List<Type /*!*/> /*!*/ ToList(TypeParamInstantiation insts)
    {
      Contract.Requires(insts != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Type>>()));
      if (insts.FormalTypeParams.Count == 0)
      {
        return EMPTY_TYPE_LIST;
      }

      List<Type /*!*/> /*!*/
        typeArgs = new List<Type /*!*/>();
      foreach (TypeVariable /*!*/ var in insts.FormalTypeParams)
      {
        Contract.Assert(var != null);
        typeArgs.Add(insts[var]);
      }

      return typeArgs;
    }

    ///////////////////////////////////////////////////////////////////////////////////

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<QuantifierExpr>() != null);
      Push(TranslateQuantifierExpr(node));
      return node;
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node = (ExistsExpr) this.VisitQuantifierExpr(node);
      return node;
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node = (ForallExpr) this.VisitQuantifierExpr(node);
      return node;
    }

    private VCExpr TranslateQuantifierExpr(QuantifierExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      List<TypeVariable /*!*/> /*!*/
        typeParams = new List<TypeVariable /*!*/>();
      foreach (TypeVariable /*!*/ v in node.TypeParameters)
      {
        Contract.Assert(v != null);
        typeParams.Add(v);
      }

      PushBoundVariableScope();

      List<VCExprVar /*!*/> /*!*/
        boundVars = new List<VCExprVar /*!*/>();
      foreach (Variable /*!*/ v in node.Dummies)
      {
        boundVars.Add(BindVariable(v));
      }

      try
      {
        List<VCTrigger /*!*/> /*!*/
          triggers = TranslateTriggers(node.Triggers);
        VCExpr /*!*/
          body = Translate(node.Body);
        VCQuantifierInfo /*!*/
          info = GenerateQuantifierInfo(node, boundVars);

        Quantifier quan;
        if (node is ForallExpr)
        {
          quan = Quantifier.ALL;
        }
        else if (node is ExistsExpr)
        {
          quan = Quantifier.EX;
        }
        else
        {
          Contract.Assert(false);
          throw new Cce.UnreachableException();
        }

        return Gen.Quantify(quan, typeParams, boundVars, triggers, info, body);
      }
      finally
      {
        PopBoundVariableScope();
      }
    }

    private List<VCTrigger /*!*/> /*!*/ TranslateTriggers(Trigger node)
    {
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCTrigger>>()));
      List<VCTrigger /*!*/> /*!*/
        res = new List<VCTrigger /*!*/>();
      Trigger curTrigger = node;
      while (curTrigger != null)
      {
        res.Add(Gen.Trigger(curTrigger.Pos, Translate(curTrigger.Tr)));
        curTrigger = curTrigger.Next;
      }

      return res;
    }

    private VCQuantifierInfo GenerateQuantifierInfo(QuantifierExpr node, List<VCExprVar> boundVars)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCQuantifierInfo>() != null);
      return new VCQuantifierInfo(
        GetQid(node),
        node.SkolemId,
        QKeyValue.FindIntAttribute(node.Attributes, "weight", 1),
        Enumerable.Range(0, boundVars.Count)
          .ToDictionary(x => boundVars[x], x => QuantifierInstantiationEngine.FindInstantiationHints(node.Dummies[x])),
        QuantifierInstantiationEngine.FindInstantiationSources(node, this));
    }

    private string GetQid(QuantifierExpr node)
    {
      List<Variable> vars = node.Dummies;
      QKeyValue attributes = node.Attributes;
      // Check for a 'qid, name' pair in attributes
      string qid = QKeyValue.FindStringAttribute(attributes, "qid");
      if (qid == null && vars.Count != 0)
      {
        // generate default name (line:column position in .bpl file)
        Variable v = vars[0];
        Contract.Assert(v != null);
        StringBuilder buf = new StringBuilder(20);
        string filename = v.tok.filename;
        if (filename == null)
        {
          filename = "unknown";
        }
        for (int i = 0; i < filename.Length; ++i)
        {
          if (filename[i] == '/' || filename[i] == '\\')
          {
            buf.Length = 0;
          }
          if (char.IsLetterOrDigit(filename[i]))
          {
            if (buf.Length == 0 && char.IsDigit(filename[i]))
            {
              // Z3 does not like QID's to start with a digit, so we prepend another character
              buf.Append('_');
            }
            buf.Append(filename[i]);
          }
        }
        buf.Append('.').Append(v.Line).Append(':').Append(v.Col);
        qid = buf.ToString();
      }
      return qid;
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() != null);

      var rhss = new List<VCExpr>();
      foreach (var e in node.Rhss)
      {
        rhss.Add(Translate(e));
      }

      PushBoundVariableScope();
      var boundVars = new List<VCExprVar>();
      foreach (var v in node.Dummies)
      {
        boundVars.Add(BindVariable(v));
      }

      var body = Translate(node.Body);
      PopBoundVariableScope();

      Contract.Assert(boundVars.Count == rhss.Count);
      var bindings = new List<VCExprLetBinding>();
      for (var i = 0; i < boundVars.Count; i++)
      {
        var b = new VCExprLetBinding(boundVars[i], rhss[i]);
        bindings.Add(b);
      }

      var let = Gen.Let(bindings, body);
      Push(let);
      return node;
    }

    ///////////////////////////////////////////////////////////////////////////////////

    public override Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Push(TranslateBvExtractExpr(node));
      return node;
    }

    private VCExpr TranslateBvExtractExpr(BvExtractExpr node)
    {
      Contract.Requires(node != null);
      Contract.Requires((node.Start <= node.End));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr /*!*/
        bv = Translate(node.Bitvector);
      return Gen.BvExtract(bv, Cce.NonNull(node.Bitvector.Type).BvBits, node.Start, node.End);
    }

    ///////////////////////////////////////////////////////////////////////////////////

    public override Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Push(TranslateBvConcatExpr(node));
      return node;
    }

    private VCExpr TranslateBvConcatExpr(BvConcatExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      VCExpr /*!*/
        bv0 = Translate(node.E0);
      VCExpr /*!*/
        bv1 = Translate(node.E1);
      return Gen.BvConcat(bv0, bv1);
    }

    ///////////////////////////////////////////////////////////////////////////////////
    // all the other cases should never happen

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }
    
    public override Cmd VisitAssumeCmd(AssumeCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override AtomicRE VisitAtomicRE(AtomicRE node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AtomicRE>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Axiom>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Type VisitBasicType(BasicType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Type VisitBvType(BvType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Block VisitBlock(Block node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Block>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public CodeExprConverter codeExprConverter = null;

    public void SetCodeExprConverter(CodeExprConverter f)
    {
      this.codeExprConverter = f;
    }

    public override Expr VisitCodeExpr(CodeExpr codeExpr)
    {
      //Contract.Requires(codeExpr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Contract.Assume(codeExprConverter != null);
      
      List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
      VCExpr e = codeExprConverter(codeExpr, bindings, isPositiveContext, new());
      Push(e);
      return codeExpr;
    }

    public override List<Block> VisitBlockSeq(List<Block> blockSeq)
    {
      //Contract.Requires(blockSeq != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<Block /*!*/> /*!*/ VisitBlockList(List<Block /*!*/> /*!*/ blocks)
    {
      //Contract.Requires(cce.NonNullElements(blocks));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Block>>()));
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override BoundVariable VisitBoundVariable(BoundVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BoundVariable>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      //Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Choice VisitChoice(Choice node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Choice>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitCommentCmd(CommentCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Constant VisitConstant(Constant node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Constant>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<CtorType>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Declaration VisitDeclaration(Declaration node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<Declaration /*!*/> /*!*/ VisitDeclarationList(List<Declaration /*!*/> /*!*/ declarationList)
    {
      //Contract.Requires(cce.NonNullElements(declarationList));
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<Declaration>>()));
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<DeclWithFormals>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Requires VisitRequires(Requires @requires)
    {
      //Contract.Requires(@requires != null);
      Contract.Ensures(Contract.Result<Requires>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      //Contract.Requires(requiresSeq != null);
      Contract.Ensures(Contract.Result<List<Requires>>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Ensures VisitEnsures(Ensures @ensures)
    {
      //Contract.Requires(@ensures != null);
      Contract.Ensures(Contract.Result<Ensures>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      //Contract.Requires(ensuresSeq != null);
      Contract.Ensures(Contract.Result<List<Ensures>>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Formal VisitFormal(Formal node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Formal>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Function VisitFunction(Function node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GlobalVariable>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override GotoCmd VisitGotoCmd(GotoCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GotoCmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitHavocCmd(HavocCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override LocalVariable VisitLocalVariable(LocalVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LocalVariable>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Type VisitMapType(MapType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<MapType>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Procedure>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Program VisitProgram(Program node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Program>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitRE(RE node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<RE> VisitRESeq(List<RE> reSeq)
    {
      //Contract.Requires(reSeq != null);
      Contract.Ensures(Contract.Result<List<RE>>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override ReturnCmd VisitReturnCmd(ReturnCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnCmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnExprCmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Sequential VisitSequential(Sequential node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Sequential>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitStateCmd(StateCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override TransferCmd VisitTransferCmd(TransferCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Trigger VisitTrigger(Trigger node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Trigger>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Type VisitType(Type node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TypedIdent>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Variable VisitVariable(Variable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
    {
      //Contract.Requires(variableSeq != null);
      Contract.Ensures(Contract.Result<List<Variable>>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }

    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      Contract.Assert(false);
      throw new Cce.UnreachableException();
    }
  }


  /////////////////////////////////////////////////////////////////////////////////

  public class IAppliableTranslator : IAppliableVisitor<VCExpr /*!*/>
  {
    private readonly Boogie2VCExprTranslator /*!*/
      BaseTranslator;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(BaseTranslator != null);
    }


    private VCExpressionGenerator /*!*/ Gen
    {
      get
      {
        Contract.Ensures(Contract.Result<VCExpressionGenerator>() != null);

        return BaseTranslator.Gen;
      }
    }

    private VCGenerationOptions GenerationOptions
    {
      get
      {
        Contract.Ensures(Contract.Result<VCGenerationOptions>() != null);

        return BaseTranslator.GenerationOptions;
      }
    }

    public IAppliableTranslator(Boogie2VCExprTranslator baseTranslator)
    {
      Contract.Requires(baseTranslator != null);
      this.BaseTranslator = baseTranslator;
    }

    ///////////////////////////////////////////////////////////////////////////////

    private List<VCExpr /*!*/> /*!*/
      args = new List<VCExpr /*!*/>();

    private List<Type /*!*/> /*!*/
      typeArgs = new List<Type /*!*/>();

    [ContractInvariantMethod]
    void ObjectInvarianet()
    {
      Contract.Invariant(args != null);
      Contract.Invariant(typeArgs != null);
    }


    public VCExpr Translate(IAppliable app, Type ty, List<VCExpr /*!*/> /*!*/ args, List<Type /*!*/> /*!*/ typeArgs)
    {
      Contract.Requires(ty != null);
      Contract.Requires(app != null);
      Contract.Requires(Cce.NonNullElements(typeArgs));
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<VCExpr>() != null);

      List<VCExpr /*!*/> /*!*/
        oldArgs = this.args;
      List<Type /*!*/> /*!*/
        oldTypeArgs = this.typeArgs;
      this.args = args;
      this.typeArgs = typeArgs;
      VCExpr /*!*/
        result = app.Dispatch<VCExpr /*!*/>(this);
      this.args = oldArgs;
      this.typeArgs = oldTypeArgs;
      return result;
    }

    ///////////////////////////////////////////////////////////////////////////////


    public VCExpr Visit(UnaryOperator unaryOperator)
    {
      //Contract.Requires(unaryOperator != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Contract.Assert(unaryOperator.Op == UnaryOperator.Opcode.Neg || unaryOperator.Op == UnaryOperator.Opcode.Not);
      Contract.Assert(this.args.Count == 1);
      if (unaryOperator.Op == UnaryOperator.Opcode.Neg)
      {
        VCExpr e = Cce.NonNull(this.args[0]);
        if (Cce.NonNull(e.Type).IsInt)
        {
          return Gen.Function(VCExpressionGenerator.SubIOp, Gen.Integer(BigNum.ZERO), e);
        }
        else
        {
          // if (cce.NonNull(e.Type).IsReal) {
          return Gen.Function(VCExpressionGenerator.SubROp, Gen.Real(BigDec.ZERO), e);
        }

        //else  {//is float
        //return Gen.Function(VCExpressionGenerator.SubFOp, Gen.Float(BigFloat.ZERO(8, 23)), e);
        //} 
      }
      else
      {
        return Gen.Not(this.args);
      }
    }

    public VCExpr Visit(BinaryOperator binaryOperator)
    {
      //Contract.Requires(binaryOperator != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return TranslateBinaryOperator(binaryOperator, this.args);
    }

    public VCExpr Visit(FunctionCall functionCall)
    {
      //Contract.Requires(functionCall != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return TranslateFunctionCall(functionCall, this.args, this.typeArgs);
    }

    public VCExpr Visit(MapSelect mapSelect)
    {
      if (GenerationOptions.Options.TypeEncodingMethod == CoreOptions.TypeEncoding.Monomorphic && args.Count == 1 && typeArgs.Count == 0)
      {
        return args[0];
      }
      return Gen.Select(this.args, this.typeArgs);
    }

    public VCExpr Visit(MapStore mapStore)
    {
      if (GenerationOptions.Options.TypeEncodingMethod == CoreOptions.TypeEncoding.Monomorphic && args.Count == 2 && typeArgs.Count == 0)
      {
        return args[1];
      }
      return Gen.Store(this.args, this.typeArgs);
    }

    public VCExpr Visit(TypeCoercion typeCoercion)
    {
      //Contract.Requires(typeCoercion != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Contract.Assert(this.args.Count == 1);
      return this.args[0];
    }

    public VCExpr Visit(ArithmeticCoercion arithCoercion)
    {
      //Contract.Requires(arithCoercion != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Contract.Assert(this.args.Count == 1);
      switch (arithCoercion.Coercion)
      {
        case ArithmeticCoercion.CoercionType.ToInt:
          return Gen.Function(VCExpressionGenerator.ToIntOp, this.args);
        case ArithmeticCoercion.CoercionType.ToReal:
          return Gen.Function(VCExpressionGenerator.ToRealOp, this.args);
        default:
          Contract.Assert(false);
          return null;
      }
    }

    public VCExpr Visit(IfThenElse ite)
    {
      //Contract.Requires(ite != null);
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      return Gen.Function(VCExpressionGenerator.IfThenElseOp, this.args);
    }
    
    public VCExpr Visit(FieldAccess fieldAccess)
    {
      var accessor = fieldAccess.Accessors[0];
      var expr = Gen.Function(new VCExprFieldAccessOp(fieldAccess.DatatypeTypeCtorDecl, accessor),
        this.args);
      for (int i = 1; i < fieldAccess.Accessors.Count; i++)
      {
        accessor = fieldAccess.Accessors[i];
        var condExpr = Gen.Function(new VCExprIsConstructorOp(fieldAccess.DatatypeTypeCtorDecl, accessor.ConstructorIndex),
          this.args);
        var thenExpr =
          Gen.Function(new VCExprFieldAccessOp(fieldAccess.DatatypeTypeCtorDecl, accessor),
            this.args);
        expr = Gen.Function(VCExpressionGenerator.IfThenElseOp, new List<VCExpr>() { condExpr, thenExpr, expr });
      }
      return expr;
    }

    public VCExpr Visit(FieldUpdate fieldUpdate)
    {
      throw new Cce.UnreachableException();
    }
    
    public VCExpr Visit(IsConstructor isConstructor)
    {
      return Gen.Function(new VCExprIsConstructorOp(isConstructor.DatatypeTypeCtorDecl, isConstructor.ConstructorIndex), this.args);
    }
    
    
    ///////////////////////////////////////////////////////////////////////////////

    private VCExpr TranslateBinaryOperator(BinaryOperator app, List<VCExpr /*!*/> /*!*/ args)
    {
      Contract.Requires(app != null);
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<VCExpr>() != null);
      Contract.Assert(args.Count == 2);
      Type t = Cce.NonNull(Cce.NonNull(args[0]).Type);

      switch (app.Op)
      {
        case BinaryOperator.Opcode.Add:
          if (t.IsInt)
          {
            return Gen.Function(VCExpressionGenerator.AddIOp, args);
          }
          else if (t.IsReal)
          {
            return Gen.Function(VCExpressionGenerator.AddROp, args);
          }
          else
          {
            //t is float
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "+"), args);
          }
        case BinaryOperator.Opcode.Sub:
          if (t.IsInt)
          {
            return Gen.Function(VCExpressionGenerator.SubIOp, args);
          }
          else if (t.IsReal)
          {
            return Gen.Function(VCExpressionGenerator.SubROp, args);
          }
          else
          {
            //t is float
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "-"), args);
          }
        case BinaryOperator.Opcode.Mul:
          if (t.IsInt)
          {
            return Gen.Function(VCExpressionGenerator.MulIOp, args);
          }
          else if (t.IsReal)
          {
            return Gen.Function(VCExpressionGenerator.MulROp, args);
          }
          else
          {
            //t is float
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "*"), args);
          }
        case BinaryOperator.Opcode.Div:
          return Gen.Function(VCExpressionGenerator.DivIOp, args);
        case BinaryOperator.Opcode.Mod:
          return Gen.Function(VCExpressionGenerator.ModOp, args);
        case BinaryOperator.Opcode.RealDiv:
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "/"), args);
          }

          VCExpr arg0 = Cce.NonNull(args[0]);
          VCExpr arg1 = Cce.NonNull(args[1]);
          if (Cce.NonNull(arg0.Type).IsInt)
          {
            arg0 = Gen.Function(VCExpressionGenerator.ToRealOp, arg0);
          }

          if (Cce.NonNull(arg1.Type).IsInt)
          {
            arg1 = Gen.Function(VCExpressionGenerator.ToRealOp, arg1);
          }

          return Gen.Function(VCExpressionGenerator.DivROp, arg0, arg1);
        case BinaryOperator.Opcode.Pow:
          return Gen.Function(VCExpressionGenerator.PowOp, args);
        case BinaryOperator.Opcode.Eq:
        case BinaryOperator.Opcode.Iff:
          // we don't distinguish between equality and equivalence at this point
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "=="), args);
          }

          return Gen.Function(VCExpressionGenerator.EqOp, args);
        case BinaryOperator.Opcode.Neq:
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "!="), args);
          }

          return Gen.Function(VCExpressionGenerator.NeqOp, args);
        case BinaryOperator.Opcode.Lt:
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "<"), args);
          }

          return Gen.Function(VCExpressionGenerator.LtOp, args);
        case BinaryOperator.Opcode.Le:
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, "<="), args);
          }

          return Gen.Function(VCExpressionGenerator.LeOp, args);
        case BinaryOperator.Opcode.Ge:
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, ">="), args);
          }

          return Gen.Function(VCExpressionGenerator.GeOp, args);
        case BinaryOperator.Opcode.Gt:
          if (t.IsFloat)
          {
            return Gen.Function(Gen.BinaryFloatOp(t.FloatSignificand, t.FloatExponent, ">"), args);
          }

          return Gen.Function(VCExpressionGenerator.GtOp, args);
        case BinaryOperator.Opcode.Imp:
          return Gen.Function(VCExpressionGenerator.ImpliesOp, args);
        case BinaryOperator.Opcode.And:
          return Gen.Function(VCExpressionGenerator.AndOp, args);
        case BinaryOperator.Opcode.Or:
          return Gen.Function(VCExpressionGenerator.OrOp, args);
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException(); // unexpected binary operator
      }
    }

    ///////////////////////////////////////////////////////////////////////////////

    private VCExpr /*!*/
      TranslateFunctionCall(FunctionCall app, List<VCExpr /*!*/> /*!*/ args, List<Type /*!*/> /*!*/ typeArgs)
    {
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Requires(Cce.NonNullElements(typeArgs));
      Contract.Requires(app != null);
      Contract.Requires((app.Func != null));
      Contract.Ensures(Contract.Result<VCExpr>() != null); // resolution must have happened

      VCExpr res = ApplyExpansion(app, args, typeArgs);
      if (res != null)
      {
        return res;
      }

      VCExprOp /*!*/
        functionOp = Gen.BoogieFunctionOp(app.Func);
      return Gen.Function(functionOp, args, typeArgs);
    }

    private VCExpr ApplyExpansion(FunctionCall app, List<VCExpr /*!*/> /*!*/ args, List<Type /*!*/> /*!*/ typeArgs)
    {
      Contract.Requires(app != null);
      Contract.Requires(Cce.NonNullElements(args));
      Contract.Requires(Cce.NonNullElements(typeArgs));
      Contract.Assert(app.Func != null); // resolution must have happened

      lock (app.Func)
      {
        var exp = app.Func.Body;
        if (exp == null)
        {
          return null;
        }

        VCExpr /*!*/
          translatedBody;
        VCExprSubstitution /*!*/
          subst = new VCExprSubstitution();
        try
        {
          BaseTranslator.PushFormalsScope();
          BaseTranslator.PushBoundVariableScope();

          // first bind the formals to VCExpr variables, which are later
          // substituted with the actual parameters
          var inParams = app.Func.InParams;
          for (int i = 0; i < inParams.Count; ++i)
          {
            subst[BaseTranslator.BindVariable(inParams[i])] = args[i];
          }

          // recursively translate the body of the expansion
          translatedBody = BaseTranslator.Translate(exp);
        }
        finally
        {
          BaseTranslator.PopFormalsScope();
          BaseTranslator.PopBoundVariableScope();
        }

        // substitute the formals with the actual parameters in the body
        var tparms = app.Func.TypeParameters;
        Contract.Assert(typeArgs.Count == tparms.Count);
        for (int i = 0; i < typeArgs.Count; ++i)
        {
          subst[tparms[i]] = typeArgs[i];
        }

        SubstitutingVCExprVisitor /*!*/
          substituter = new SubstitutingVCExprVisitor(Gen);
        return substituter.Mutate(translatedBody, subst);
      }
    }
  }
}