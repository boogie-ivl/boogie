using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie
{
  [ContractClass(typeof(VisitorContracts))]
  /// <summary>
  /// Base for all classes that process the Absy using the visitor pattern.
  /// </summary>
  public abstract class Visitor
  {
    /// <summary>
    /// Switches on node.NodeType to call a visitor method that has been specialized for node.
    /// </summary>
    /// <param name="a">The Absy node to be visited.</param>
    /// <returns> Returns null if node is null. Otherwise returns an updated node (possibly a different object).</returns>
    public abstract Absy /*!*/ Visit(Absy /*!*/ node);

    /// <summary>
    /// Transfers the state from one visitor to another. This enables separate visitor instances to cooperative process a single IR.
    /// </summary>
    public virtual void TransferStateTo(Visitor targetVisitor)
    {
    }

    public virtual IList<Expr> VisitExprSeq(IList<Expr> list)
    {
      Contract.Requires(list != null);
      Contract.Ensures(Contract.Result<IList<Expr>>() != null);
      lock (list)
      {
        for (int i = 0, n = list.Count; i < n; i++)
        {
          list[i] = (Expr) this.Visit(Cce.NonNull(list[i]));
        }
      }

      return list;
    }
  }

  [ContractClassFor(typeof(Visitor))]
  abstract class VisitorContracts : Visitor
  {
    public override Absy Visit(Absy node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Absy>() != null);

      throw new System.NotImplementedException();
    }
  }

  /// <summary>
  /// Walks an IR, mutating it into a new form. (For a subclass that does not mutate the IR, see ReadOnlyVisitor.)
  /// </summary>   
  public abstract class StandardVisitor : Visitor
  {
    public Visitor callingVisitor;

    public StandardVisitor()
    {
    }

    public StandardVisitor(Visitor callingVisitor)
    {
      this.callingVisitor = callingVisitor;
    }

    public override Absy Visit(Absy node)
    {
      return node.StdDispatch(this);
    }

    public virtual Cmd VisitAssertCmd(AssertCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }
    
    public virtual Cmd VisitRevealCmd(HideRevealCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return node;
    }
    
    public virtual Cmd VisitChangeScopeCmd(ChangeScope node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return node;
    }

    public virtual Cmd VisitAssignCmd(AssignCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      for (int i = 0; i < node.Lhss.Count; ++i)
      {
        node.SetLhs(i, Cce.NonNull((AssignLhs) this.Visit(node.Lhss[i])));
        node.SetRhs(i, Cce.NonNull((Expr /*!*/) this.VisitExpr(node.Rhss[i])));
      }
      VisitAttributes(node);
      return node;
    }

    public virtual Cmd VisitUnpackCmd(UnpackCmd node)
    {
      node.Lhs = (NAryExpr)this.Visit(node.Lhs);
      node.Rhs = (Expr)this.Visit(node.Rhs);
      VisitAttributes(node);
      return node;
    }
    
    public virtual Cmd VisitAssumeCmd(AssumeCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }

    public virtual AtomicRE VisitAtomicRE(AtomicRE node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AtomicRE>() != null);
      node.b = this.VisitBlock(node.b);
      return node;
    }

    public virtual Axiom VisitAxiom(Axiom node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Axiom>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }

    public virtual Type VisitBasicType(BasicType node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }

    public virtual Type VisitFloatType(FloatType node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }

    public virtual Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.E0 = this.VisitExpr(node.E0);
      node.E1 = this.VisitExpr(node.E1);
      return node;
    }

    public virtual Type VisitBvType(BvType node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }

    public virtual Type VisitBvTypeProxy(BvTypeProxy node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        return (Type) this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public virtual Block VisitBlock(Block node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Block>() != null);
      node.Cmds = this.VisitCmdSeq(node.Cmds);
      node.TransferCmd = (TransferCmd) this.Visit(Cce.NonNull(node.TransferCmd));
      return node;
    }

    public virtual Expr VisitCodeExpr(CodeExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.LocVars = this.VisitVariableSeq(node.LocVars);
      node.Blocks = this.VisitBlockList(node.Blocks);
      return node;
    }

    public virtual List<Block> VisitBlockSeq(List<Block> blockSeq)
    {
      Contract.Requires(blockSeq != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);
      lock (blockSeq)
      {
        for (int i = 0, n = blockSeq.Count; i < n; i++)
        {
          blockSeq[i] = this.VisitBlock(Cce.NonNull(blockSeq[i]));
        }
      }

      return blockSeq;
    }

    public virtual List<Block /*!*/> /*!*/ VisitBlockList(List<Block /*!*/> /*!*/ blocks)
    {
      Contract.Requires(blocks != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);
      for (int i = 0, n = blocks.Count; i < n; i++)
      {
        blocks[i] = this.VisitBlock(blocks[i]);
      }

      return blocks;
    }

    public virtual BoundVariable VisitBoundVariable(BoundVariable node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BoundVariable>() != null);
      node = (BoundVariable) this.VisitVariable(node);
      return node;
    }

    public virtual Cmd VisitCallCmd(CallCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      for (int i = 0; i < node.Ins.Count; ++i)
      {
        if (node.Ins[i] != null)
        {
          node.Ins[i] = this.VisitExpr(Cce.NonNull(node.Ins[i]));
        }
      }

      for (int i = 0; i < node.Outs.Count; ++i)
      {
        if (node.Outs[i] != null)
        {
          node.Outs[i] = (IdentifierExpr) this.VisitIdentifierExpr(Cce.NonNull(node.Outs[i]));
        }
      }
      VisitAttributes(node);
      return node;
    }

    public virtual List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds)
    {
      for (int i = 0; i < callCmds.Count; i++)
      {
        callCmds[i] = (CallCmd)VisitCallCmd(callCmds[i]);
      }
      return callCmds;
    }

    public virtual List<AssertCmd> VisitAssertCmdSeq(List<AssertCmd> assertCmds)
    {
      for (int i = 0; i < assertCmds.Count; i++)
      {
        assertCmds[i] = (AssertCmd)VisitAssertCmd(assertCmds[i]);
      }
      return assertCmds;
    }

    public virtual Cmd VisitParCallCmd(ParCallCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      for (int i = 0; i < node.CallCmds.Count; i++)
      {
        if (node.CallCmds[i] != null)
        {
          node.CallCmds[i] = (CallCmd) this.VisitCallCmd(node.CallCmds[i]);
        }
      }
      VisitAttributes(node);
      return node;
    }

    public virtual List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      lock (cmdSeq)
      {
        for (int i = 0, n = cmdSeq.Count; i < n; i++)
        {
          cmdSeq[i] = (Cmd) this.Visit(
            Cce.NonNull(cmdSeq[i])); // call general Visit so subtypes of Cmd get visited by their particular visitor
        }
      }

      return cmdSeq;
    }

    public virtual Choice VisitChoice(Choice node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Choice>() != null);
      node.rs = this.VisitRESeq(node.rs);
      return node;
    }

    public virtual Cmd VisitCommentCmd(CommentCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return node;
    }

    public virtual Constant VisitConstant(Constant node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Constant>() != null);
      return node;
    }

    public virtual CtorType VisitCtorType(CtorType node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<CtorType>() != null);
      lock (node)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = Cce.NonNull((Type /*!*/) this.Visit(node.Arguments[i]));
        }
      }

      return node;
    }

    public virtual Declaration VisitDeclaration(Declaration node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return node;
    }

    public virtual List<Declaration /*!*/> /*!*/ VisitDeclarationList(List<Declaration /*!*/> /*!*/ declarationList)
    {
      Contract.Requires(declarationList != null);
      Contract.Ensures(Contract.Result<List<Declaration>>() != null);
      for (int i = 0, n = declarationList.Count; i < n; i++)
      {
        declarationList[i] = Cce.NonNull((Declaration /*!*/) this.Visit(declarationList[i]));
      }

      return declarationList;
    }

    public virtual DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<DeclWithFormals>() != null);
      node.InParams = this.VisitVariableSeq(node.InParams);
      node.OutParams = this.VisitVariableSeq(node.OutParams);
      return node;
    }

    public virtual Expr VisitExistsExpr(ExistsExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node = (ExistsExpr) this.VisitQuantifierExpr(node);
      return node;
    }

    public virtual Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.Bitvector = this.VisitExpr(node.Bitvector);
      return node;
    }

    public virtual Expr VisitExpr(Expr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      Expr e = (Expr) this.Visit(node);
      return e;
    }

    public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
    {
      //Contract.Requires(exprSeq != null);
      Contract.Ensures(Contract.Result<IList<Expr>>() != null);
      for (int i = 0, n = exprSeq.Count; i < n; i++)
      {
        exprSeq[i] = this.VisitExpr(Cce.NonNull(exprSeq[i]));
      }

      return exprSeq;
    }

    public virtual Requires VisitRequires(Requires @requires)
    {
      Contract.Requires(@requires != null);
      Contract.Ensures(Contract.Result<Requires>() != null);
      @requires.Condition = this.VisitExpr(@requires.Condition);
      return @requires;
    }

    public virtual List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      Contract.Requires(requiresSeq != null);
      Contract.Ensures(Contract.Result<List<Requires>>() != null);
      for (int i = 0, n = requiresSeq.Count; i < n; i++)
      {
        requiresSeq[i] = this.VisitRequires(requiresSeq[i]);
      }

      return requiresSeq;
    }

    public virtual Ensures VisitEnsures(Ensures @ensures)
    {
      Contract.Requires(@ensures != null);
      Contract.Ensures(Contract.Result<Ensures>() != null);
      @ensures.Condition = this.VisitExpr(@ensures.Condition);
      return @ensures;
    }

    public virtual List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      Contract.Requires(ensuresSeq != null);
      Contract.Ensures(Contract.Result<List<Ensures>>() != null);
      for (int i = 0, n = ensuresSeq.Count; i < n; i++)
      {
        ensuresSeq[i] = this.VisitEnsures(ensuresSeq[i]);
      }

      return ensuresSeq;
    }

    public virtual Expr VisitForallExpr(ForallExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node = (ForallExpr) this.VisitQuantifierExpr(node);
      return node;
    }

    public virtual Expr VisitLambdaExpr(LambdaExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node = (LambdaExpr) this.VisitBinderExpr(node);
      return node;
    }

    public virtual Expr VisitLetExpr(LetExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.Rhss = this.VisitExprSeq(node.Rhss);
      node.Dummies = this.VisitVariableSeq(node.Dummies);
      node.Body = this.VisitExpr(node.Body);
      VisitAttributes(node);
      return node;
    }

    public virtual Formal VisitFormal(Formal node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Formal>() != null);
      return node;
    }

    public virtual Function VisitFunction(Function node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      node = (Function) this.VisitDeclWithFormals(node);
      if (node.Body != null)
      {
        Contract.Assert(node.DefinitionBody == null);
        node.Body = this.VisitExpr(node.Body);
      }
      else if (node.DefinitionBody != null)
      {
        node.DefinitionBody = (NAryExpr) this.VisitExpr(node.DefinitionBody);
      }
      return node;
    }

    public virtual GlobalVariable VisitGlobalVariable(GlobalVariable node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GlobalVariable>() != null);
      node = (GlobalVariable) this.VisitVariable(node);
      return node;
    }

    public virtual GotoCmd VisitGotoCmd(GotoCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GotoCmd>() != null);
      // do not visit the labelTargets, or control-flow loops will lead to a looping visitor
      return node;
    }

    public virtual Cmd VisitHavocCmd(HavocCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Vars = this.VisitIdentifierExprSeq(node.Vars);
      return node;
    }

    public virtual Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      if (node.Decl != null)
      {
        node.Decl = this.VisitVariable(node.Decl);
      }

      return node;
    }

    public virtual List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq)
    {
      Contract.Requires(identifierExprSeq != null);
      Contract.Ensures(Contract.Result<List<IdentifierExpr>>() != null);
      lock (identifierExprSeq)
      {
        for (int i = 0, n = identifierExprSeq.Count; i < n; i++)
        {
          identifierExprSeq[i] = (IdentifierExpr) this.VisitIdentifierExpr(Cce.NonNull(identifierExprSeq[i]));
        }
      }

      return identifierExprSeq;
    }

    public virtual Implementation VisitImplementation(Implementation node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      node.LocVars = this.VisitVariableSeq(node.LocVars);
      node.Blocks = this.VisitBlockList(node.Blocks);
      node.Proc = (Procedure)node.Proc.StdDispatch(this);
      node = (Implementation) this.VisitDeclWithFormals(node); // do this first or last?
      VisitAttributes(node);
      return node;
    }

    public virtual Expr VisitLiteralExpr(LiteralExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return node;
    }

    public virtual LocalVariable VisitLocalVariable(LocalVariable node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LocalVariable>() != null);
      return node;
    }

    public virtual AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      node.Map = Cce.NonNull((AssignLhs) this.Visit(node.Map));
      for (int i = 0; i < node.Indexes.Count; ++i)
      {
        node.Indexes[i] = Cce.NonNull((Expr) this.VisitExpr(node.Indexes[i]));
      }

      return node;
    }

    public virtual AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      node.Datatype = Cce.NonNull((AssignLhs) this.Visit(node.Datatype));
      return node;
    }
    
    public virtual Type VisitMapType(MapType node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<MapType>() != null);
      // not doing anything about the bound variables ... maybe
      // these should be visited as well ...
      //
      // NOTE: when overriding this method, you have to make sure that
      // the bound variables of the map type are updated correctly
      lock (node.Arguments)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = Cce.NonNull((Type /*!*/) this.Visit(node.Arguments[i]));
        }
      }

      node.Result = Cce.NonNull((Type /*!*/) this.Visit(node.Result));
      return node;
    }

    public virtual Type VisitMapTypeProxy(MapTypeProxy node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        return (Type) this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public virtual Expr VisitNAryExpr(NAryExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.Args = this.VisitExprSeq(node.Args);
      return node;
    }

    public virtual Expr VisitOldExpr(OldExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }

    public virtual Procedure VisitProcedure(Procedure node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Procedure>() != null);
      node.Ensures = this.VisitEnsuresSeq(node.Ensures);
      node.InParams = this.VisitVariableSeq(node.InParams);
      node.Modifies = this.VisitIdentifierExprSeq(node.Modifies);
      node.OutParams = this.VisitVariableSeq(node.OutParams);
      node.Requires = this.VisitRequiresSeq(node.Requires);
      VisitAttributes(node);
      return node;
    }

    public virtual ActionDeclRef VisitActionDeclRef(ActionDeclRef node)
    {
      return node;
    }

    public virtual Procedure VisitActionDecl(ActionDecl node)
    {
      for (int i = 0; i < node.Creates.Count; i++)
      {
        node.Creates[i] = VisitActionDeclRef(node.Creates[i]);
      }
      if (node.RefinedAction != null)
      {
        node.RefinedAction = VisitActionDeclRef(node.RefinedAction);
      }
      if (node.InvariantAction != null)
      {
        node.InvariantAction = VisitActionDeclRef(node.InvariantAction);
      }
      node.YieldRequires = VisitCallCmdSeq(node.YieldRequires);
      node.Asserts = VisitAssertCmdSeq(node.Asserts);
      return VisitProcedure(node);
    }

    public virtual YieldingLoop VisitYieldingLoop(YieldingLoop node)
    {
      node.YieldInvariants = VisitCallCmdSeq(node.YieldInvariants);
      return node;
    }

    public virtual Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node)
    {
      foreach (var block in node.Keys)
      {
        node[block] = VisitYieldingLoop(node[block]);
      }
      return node;
    }

    public virtual HashSet<Variable> VisitVariableSet(HashSet<Variable> node)
    {
      return node;
    }

    public virtual Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
    {
      node.YieldRequires = VisitCallCmdSeq(node.YieldRequires);
      node.YieldEnsures = VisitCallCmdSeq(node.YieldEnsures);
      node.YieldPreserves = VisitCallCmdSeq(node.YieldPreserves);
      node.RefinedAction = VisitActionDeclRef(node.RefinedAction);
      node.VisibleFormals = VisitVariableSet(node.VisibleFormals);
      node.YieldingLoops = VisitYieldingLoops(node.YieldingLoops);
      return VisitProcedure(node);
    }

    public virtual Procedure VisitYieldInvariantDecl(YieldInvariantDecl node)
    {
      return VisitProcedure(node);
    }
    
    public virtual Program VisitProgram(Program node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Program>() != null);
      var decls = node.TopLevelDeclarations.ToList();
      node.ClearTopLevelDeclarations();
      node.AddTopLevelDeclarations(this.VisitDeclarationList(decls));
      return node;
    }

    public virtual QKeyValue VisitQKeyValue(QKeyValue node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<QKeyValue>() != null);
      var newParams = new List<object>();
      for (int i = 0, n = node.Params.Count; i < n; i++)
      {
        var e = node.Params[i] as Expr;
        newParams.Add(e != null ? this.Visit(e) : node.Params[i]);
      }

      node.ClearParams();
      node.AddParams(newParams);
      if (node.Next != null)
      {
        node.Next = (QKeyValue) this.Visit(node.Next);
      }

      return node;
    }

    public virtual Expr VisitBinderExpr(BinderExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BinderExpr>() != null);
      node.Body = this.VisitExpr(node.Body);
      node.Dummies = this.VisitVariableSeq(node.Dummies);
      //node.Type = this.VisitType(node.Type);
      VisitAttributes(node);
      return node;
    }

    public virtual QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<QuantifierExpr>() != null);
      node = Cce.NonNull((QuantifierExpr) this.VisitBinderExpr(node));
      if (node.Triggers != null)
      {
        node.Triggers = this.VisitTrigger(node.Triggers);
      }

      return node;
    }

    public virtual Cmd VisitRE(RE node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd) this.Visit(node); // Call general visit so subtypes get visited by their particular visitor
    }

    public virtual List<RE> VisitRESeq(List<RE> reSeq)
    {
      Contract.Requires(reSeq != null);
      Contract.Ensures(Contract.Result<List<RE>>() != null);
      for (int i = 0, n = reSeq.Count; i < n; i++)
      {
        reSeq[i] = (RE) this.VisitRE(Cce.NonNull(reSeq[i]));
      }

      return reSeq;
    }

    public virtual ReturnCmd VisitReturnCmd(ReturnCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnCmd>() != null);
      return (ReturnCmd) this.VisitTransferCmd(node);
    }

    public virtual ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnExprCmd>() != null);
      node.Expr = this.VisitExpr(node.Expr);
      return node;
    }

    public virtual Sequential VisitSequential(Sequential node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Sequential>() != null);
      node.first = (RE) this.VisitRE(node.first);
      node.second = (RE) this.VisitRE(node.second);
      return node;
    }

    public virtual AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      node.AssignedVariable =
        (IdentifierExpr) this.VisitIdentifierExpr(node.AssignedVariable);
      return node;
    }

    public virtual Cmd VisitStateCmd(StateCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Locals = this.VisitVariableSeq(node.Locals);
      node.Cmds = this.VisitCmdSeq(node.Cmds);
      return node;
    }

    public virtual TransferCmd VisitTransferCmd(TransferCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      return node;
    }

    public virtual Trigger VisitTrigger(Trigger node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Trigger>() != null);
      Trigger origNext = node.Next;
      if (origNext != null)
      {
        Trigger newNext = this.VisitTrigger(origNext);
        if (newNext != origNext)
        {
          node = new Trigger(node.tok, node.Pos, node.Tr.ToList());
          node.Next = newNext;
        }
      }

      node.Tr = this.VisitExprSeq(node.Tr.ToList());
      return node;
    }

    // called by default for all nullary type constructors and type variables
    public virtual Type VisitType(Type node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return node;
    }

    public virtual TypedIdent VisitTypedIdent(TypedIdent node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TypedIdent>() != null);
      node.Type = (Type) this.Visit(node.Type);
      return node;
    }

    public virtual Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return this.VisitDeclaration(node);
    }

    public virtual Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      node.ExpandedType = Cce.NonNull((Type /*!*/) this.Visit(node.ExpandedType));
      lock (node.Arguments)
      {
        for (int i = 0; i < node.Arguments.Count; ++i)
        {
          node.Arguments[i] = Cce.NonNull((Type /*!*/) this.Visit(node.Arguments[i]));
        }
      }

      return node;
    }

    public virtual Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return this.VisitDeclaration(node);
    }

    public virtual Type VisitTypeVariable(TypeVariable node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }

    public virtual Type VisitTypeProxy(TypeProxy node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        return Cce.NonNull((Type /*!*/) this.Visit(node.ProxyFor));
      }

      return this.VisitType(node);
    }

    public virtual Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      return this.VisitType(node);
    }

    public virtual Variable VisitVariable(Variable node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      node.TypedIdent = this.VisitTypedIdent(node.TypedIdent);
      return node;
    }

    public virtual List<Variable> VisitVariableSeq(List<Variable> variableSeq)
    {
      Contract.Requires(variableSeq != null);
      Contract.Ensures(Contract.Result<List<Variable>>() != null);
      lock (variableSeq)
      {
        for (int i = 0, n = variableSeq.Count; i < n; i++)
        {
          variableSeq[i] = this.VisitVariable(Cce.NonNull(variableSeq[i]));
        }
      }

      return variableSeq;
    }

    public virtual Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Ensures = this.VisitEnsures(node.Ensures);
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }

    public virtual Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      node.Requires = this.VisitRequires(node.Requires);
      node.Expr = this.VisitExpr(node.Expr);
      VisitAttributes(node);
      return node;
    }

    /*
     * VisitAttributes is being called in the visitor of those subtypes of Cmd
     * and Expr that implement ICarriesAttributes. This behavior is introduced so
     * that hints for pool-based quantifier instantiation present in attributes
     * are processed naturally during monomorphization and inlining. There
     * are other subtypes of Absy that implement ICarriesAttributes; if
     * necessary, this method could be in the visitor for those types also.
     */
    private void VisitAttributes(ICarriesAttributes node)
    {
      if (node.Attributes != null)
      {
        node.Attributes = VisitQKeyValue(node.Attributes);
      }
    }
  }

  /// <summary>
  /// VarDeclOnceStandardVisitor is like StandardVisitor, except
  ///   -- it does not visit a variable's declaration when visiting an `IdentifierExpr`, and
  ///   -- it visits the `where` clause (if any) when visiting a `TypedIdent`.
  /// </summary>
  public abstract class VarDeclOnceStandardVisitor : StandardVisitor
  {
    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      return node;
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node) {
      node = base.VisitTypedIdent(node);
      if (node.WhereExpr != null) {
        node.WhereExpr = (Expr) Visit(node.WhereExpr);
      }
      return node;
    }
  }

  /// <summary>
  /// A ReadOnlyVisitor visits all the nodes of a given Absy.  The visitor may collect information from
  /// the nodes, may change fields contained in the data structure, but may not replace any nodes in the
  /// data structure.  To enforce this, all Visit...(node) methods have a postcondition that says that
  /// the return value is equal to the given "node".
  /// </summary>
  public abstract class ReadOnlyVisitor : StandardVisitor
  {
    public ReadOnlyVisitor()
    {
    }

    public ReadOnlyVisitor(Visitor callingVisitor)
    {
      this.callingVisitor = callingVisitor;
    }

    public override Absy Visit(Absy node)
    {
      Contract.Ensures(Contract.Result<Absy>() == node);
      return node.StdDispatch(this);
    }

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      for (int i = 0; i < node.Lhss.Count; ++i)
      {
        this.Visit(node.Lhss[i]);
        this.VisitExpr(node.Rhss[i]);
      }
      return node;
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      this.VisitExpr(node.Lhs);
      this.VisitExpr(node.Rhs);
      return node;
    }

    public override Cmd VisitAssumeCmd(AssumeCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override AtomicRE VisitAtomicRE(AtomicRE node)
    {
      Contract.Ensures(Contract.Result<AtomicRE>() == node);
      this.VisitBlock(node.b);
      return node;
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      Contract.Ensures(Contract.Result<Axiom>() == node);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Type VisitBasicType(BasicType node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      return this.VisitType(node);
    }

    public override Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      this.VisitExpr(node.E0);
      this.VisitExpr(node.E1);
      return node;
    }

    public override Type VisitBvType(BvType node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      return this.VisitType(node);
    }

    public override Type VisitBvTypeProxy(BvTypeProxy node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public override Block VisitBlock(Block node)
    {
      Contract.Ensures(Contract.Result<Block>() == node);
      this.VisitCmdSeq(node.Cmds);
      this.Visit(Cce.NonNull(node.TransferCmd));
      return node;
    }

    public override Expr VisitCodeExpr(CodeExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      this.VisitVariableSeq(node.LocVars);
      this.VisitBlockList(node.Blocks);
      return node;
    }

    public override List<Block> VisitBlockSeq(List<Block> blockSeq)
    {
      Contract.Ensures(Contract.Result<List<Block>>() == blockSeq);
      for (int i = 0, n = blockSeq.Count; i < n; i++)
      {
        this.VisitBlock(Cce.NonNull(blockSeq[i]));
      }

      return blockSeq;
    }

    public override List<Block /*!*/> /*!*/ VisitBlockList(List<Block /*!*/> /*!*/ blocks)
    {
      Contract.Ensures(Contract.Result<List<Block>>() == blocks);
      for (int i = 0, n = blocks.Count; i < n; i++)
      {
        this.VisitBlock(blocks[i]);
      }

      return blocks;
    }

    public override BoundVariable VisitBoundVariable(BoundVariable node)
    {
      Contract.Ensures(Contract.Result<BoundVariable>() == node);
      return (BoundVariable) this.VisitVariable(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      for (int i = 0; i < node.Ins.Count; ++i)
      {
        if (node.Ins[i] != null)
        {
          this.VisitExpr(node.Ins[i]);
        }
      }

      for (int i = 0; i < node.Outs.Count; ++i)
      {
        if (node.Outs[i] != null)
        {
          this.VisitIdentifierExpr(node.Outs[i]);
        }
      }

      return node;
    }

    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      for (int i = 0; i < node.CallCmds.Count; i++)
      {
        if (node.CallCmds[i] != null)
        {
          this.VisitCallCmd(node.CallCmds[i]);
        }
      }

      return node;
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      Contract.Ensures(Contract.Result<List<Cmd>>() == cmdSeq);
      for (int i = 0, n = cmdSeq.Count; i < n; i++)
      {
        this.Visit(Cce.NonNull(
          cmdSeq[i])); // call general Visit so subtypes of Cmd get visited by their particular visitor
      }

      return cmdSeq;
    }

    public override Choice VisitChoice(Choice node)
    {
      Contract.Ensures(Contract.Result<Choice>() == node);
      this.VisitRESeq(node.rs);
      return node;
    }

    public override Cmd VisitCommentCmd(CommentCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      return node;
    }

    public override Constant VisitConstant(Constant node)
    {
      Contract.Ensures(Contract.Result<Constant>() == node);
      return node;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      Contract.Ensures(Contract.Result<CtorType>() == node);
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        this.Visit(node.Arguments[i]);
      }

      return node;
    }

    public override Declaration VisitDeclaration(Declaration node)
    {
      Contract.Ensures(Contract.Result<Declaration>() == node);
      return node;
    }

    public override List<Declaration /*!*/> /*!*/ VisitDeclarationList(List<Declaration /*!*/> /*!*/ declarationList)
    {
      Contract.Ensures(Contract.Result<List<Declaration>>() == declarationList);
      for (int i = 0, n = declarationList.Count; i < n; i++)
      {
        this.Visit(declarationList[i]);
      }

      return declarationList;
    }

    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      Contract.Ensures(Contract.Result<DeclWithFormals>() == node);
      this.VisitVariableSeq(node.InParams);
      this.VisitVariableSeq(node.OutParams);
      return node;
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      return (ExistsExpr) this.VisitQuantifierExpr(node);
    }

    public override Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      this.VisitExpr(node.Bitvector);
      return node;
    }

    public override Expr VisitExpr(Expr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      return (Expr) this.Visit(node);
    }

    public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
    {
      Contract.Ensures(Contract.Result<IList<Expr>>() == exprSeq);
      for (int i = 0, n = exprSeq.Count; i < n; i++)
      {
        this.VisitExpr(Cce.NonNull(exprSeq[i]));
      }

      return exprSeq;
    }

    public override Requires VisitRequires(Requires requires)
    {
      Contract.Ensures(Contract.Result<Requires>() == requires);
      this.VisitExpr(requires.Condition);
      return requires;
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      Contract.Ensures(Contract.Result<List<Requires>>() == requiresSeq);
      for (int i = 0, n = requiresSeq.Count; i < n; i++)
      {
        this.VisitRequires(requiresSeq[i]);
      }

      return requiresSeq;
    }

    public override Ensures VisitEnsures(Ensures ensures)
    {
      Contract.Ensures(Contract.Result<Ensures>() == ensures);
      this.VisitExpr(ensures.Condition);
      return ensures;
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      Contract.Ensures(Contract.Result<List<Ensures>>() == ensuresSeq);
      for (int i = 0, n = ensuresSeq.Count; i < n; i++)
      {
        this.VisitEnsures(ensuresSeq[i]);
      }

      return ensuresSeq;
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      return (ForallExpr) this.VisitQuantifierExpr(node);
    }

    public override Expr VisitLambdaExpr(LambdaExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      return this.VisitBinderExpr(node);
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      this.VisitExprSeq(node.Rhss);
      this.VisitVariableSeq(node.Dummies);
      this.VisitExpr(node.Body);
      return node;
    }

    public override Formal VisitFormal(Formal node)
    {
      Contract.Ensures(Contract.Result<Formal>() == node);
      return node;
    }

    public override Function VisitFunction(Function node)
    {
      Contract.Ensures(Contract.Result<Function>() == node);
      node = (Function) this.VisitDeclWithFormals(node);
      if (node.Body != null)
      {
        Contract.Assert(node.DefinitionBody == null);
        this.VisitExpr(node.Body);
      }
      else if (node.DefinitionBody != null)
      {
        this.VisitExpr(node.DefinitionBody);
      }

      return node;
    }

    public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
    {
      Contract.Ensures(Contract.Result<GlobalVariable>() == node);
      return (GlobalVariable) this.VisitVariable(node);
    }

    public override GotoCmd VisitGotoCmd(GotoCmd node)
    {
      Contract.Ensures(Contract.Result<GotoCmd>() == node);
      // do not visit the labelTargets, or control-flow loops will lead to a looping visitor
      return node;
    }

    public override Cmd VisitHavocCmd(HavocCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      this.VisitIdentifierExprSeq(node.Vars);
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      if (node.Decl != null)
      {
        this.VisitVariable(node.Decl);
      }

      return node;
    }

    public override List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq)
    {
      Contract.Ensures(Contract.Result<List<IdentifierExpr>>() == identifierExprSeq);
      for (int i = 0, n = identifierExprSeq.Count; i < n; i++)
      {
        this.VisitIdentifierExpr(Cce.NonNull(identifierExprSeq[i]));
      }

      return identifierExprSeq;
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      Contract.Ensures(Contract.Result<Implementation>() == node);
      this.VisitVariableSeq(node.LocVars);
      this.VisitBlockList(node.Blocks);
      node.Proc = (Procedure)node.Proc.StdDispatch(this);
      return (Implementation) this.VisitDeclWithFormals(node); // do this first or last?
    }

    public override Expr VisitLiteralExpr(LiteralExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      return node;
    }

    public override LocalVariable VisitLocalVariable(LocalVariable node)
    {
      Contract.Ensures(Contract.Result<LocalVariable>() == node);
      return node;
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      Contract.Ensures(Contract.Result<AssignLhs>() == node);
      this.Visit(node.Map);
      for (int i = 0; i < node.Indexes.Count; ++i)
      {
        this.VisitExpr(node.Indexes[i]);
      }

      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      Contract.Ensures(Contract.Result<MapType>() == node);
      // not doing anything about the bound variables ... maybe
      // these should be visited as well ...
      //
      // NOTE: when overriding this method, you have to make sure that
      // the bound variables of the map type are updated correctly
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        this.Visit(node.Arguments[i]);
      }

      this.Visit(node.Result);
      return node;
    }

    public override Type VisitMapTypeProxy(MapTypeProxy node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      this.VisitExprSeq(node.Args);
      return node;
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() == node);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      Contract.Ensures(Contract.Result<Procedure>() == node);
      this.VisitEnsuresSeq(node.Ensures);
      this.VisitVariableSeq(node.InParams);
      this.VisitIdentifierExprSeq(node.Modifies);
      this.VisitVariableSeq(node.OutParams);
      this.VisitRequiresSeq(node.Requires);
      return node;
    }

    public override Program VisitProgram(Program node)
    {
      Contract.Ensures(Contract.Result<Program>() == node);
      this.VisitDeclarationList(node.TopLevelDeclarations.ToList());
      return node;
    }

    public override QKeyValue VisitQKeyValue(QKeyValue node)
    {
      Contract.Ensures(Contract.Result<QKeyValue>() == node);
      for (int i = 0, n = node.Params.Count; i < n; i++)
      {
        var e = node.Params[i] as Expr;
        if (e != null)
        {
          this.Visit(e);
        }
      }

      if (node.Next != null)
      {
        this.Visit(node.Next);
      }

      return node;
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      Contract.Ensures(Contract.Result<BinderExpr>() == node);
      this.VisitExpr(node.Body);
      this.VisitVariableSeq(node.Dummies);
      // this.VisitType(node.Type);
      return node;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      Contract.Ensures(Contract.Result<QuantifierExpr>() == node);
      this.VisitBinderExpr(node);
      if (node.Triggers != null)
      {
        this.VisitTrigger(node.Triggers);
      }

      return node;
    }

    public override Cmd VisitRE(RE node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      return (Cmd) this.Visit(node); // Call general visit so subtypes get visited by their particular visitor
    }

    public override List<RE> VisitRESeq(List<RE> reSeq)
    {
      Contract.Ensures(Contract.Result<List<RE>>() == reSeq);
      for (int i = 0, n = reSeq.Count; i < n; i++)
      {
        this.VisitRE(Cce.NonNull(reSeq[i]));
      }

      return reSeq;
    }

    public override ReturnCmd VisitReturnCmd(ReturnCmd node)
    {
      Contract.Ensures(Contract.Result<ReturnCmd>() == node);
      return (ReturnCmd) this.VisitTransferCmd(node);
    }

    public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
    {
      Contract.Ensures(Contract.Result<ReturnExprCmd>() == node);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Sequential VisitSequential(Sequential node)
    {
      Contract.Ensures(Contract.Result<Sequential>() == node);
      this.VisitRE(node.first);
      this.VisitRE(node.second);
      return node;
    }

    public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
    {
      Contract.Ensures(Contract.Result<AssignLhs>() == node);
      this.VisitIdentifierExpr(node.AssignedVariable);
      return node;
    }

    public override Cmd VisitStateCmd(StateCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      this.VisitVariableSeq(node.Locals);
      this.VisitCmdSeq(node.Cmds);
      return node;
    }

    public override TransferCmd VisitTransferCmd(TransferCmd node)
    {
      Contract.Ensures(Contract.Result<TransferCmd>() == node);
      return node;
    }

    public override Trigger VisitTrigger(Trigger node)
    {
      Contract.Ensures(Contract.Result<Trigger>() == node);
      Trigger origNext = node.Next;
      if (origNext != null)
      {
        this.VisitTrigger(origNext);
      }

      this.VisitExprSeq(node.Tr.ToList());
      return node;
    }

    // called by default for all nullary type constructors and type variables
    public override Type VisitType(Type node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      return node;
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node)
    {
      Contract.Ensures(Contract.Result<TypedIdent>() == node);
      this.Visit(node.Type);
      return node;
    }

    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      Contract.Ensures(Contract.Result<Declaration>() == node);
      return this.VisitDeclaration(node);
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      node.ExpandedType = Cce.NonNull((Type /*!*/) this.Visit(node.ExpandedType));
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        this.Visit(node.Arguments[i]);
      }

      return node;
    }

    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      Contract.Ensures(Contract.Result<Declaration>() == node);
      return this.VisitDeclaration(node);
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      return this.VisitType(node);
    }

    public override Type VisitTypeProxy(TypeProxy node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      // if the type proxy is instantiated with some more
      // specific type, we visit the instantiation
      if (node.ProxyFor != null)
      {
        this.Visit(node.ProxyFor);
      }

      return this.VisitType(node);
    }

    public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
    {
      Contract.Ensures(Contract.Result<Type>() == node);
      return this.VisitType(node);
    }

    public override Variable VisitVariable(Variable node)
    {
      Contract.Ensures(Contract.Result<Variable>() == node);
      this.VisitTypedIdent(node.TypedIdent);
      return node;
    }

    public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
    {
      Contract.Ensures(Contract.Result<List<Variable>>() == variableSeq);
      for (int i = 0, n = variableSeq.Count; i < n; i++)
      {
        this.VisitVariable(Cce.NonNull(variableSeq[i]));
      }

      return variableSeq;
    }

    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      this.VisitEnsures(node.Ensures);
      this.VisitExpr(node.Expr);
      return node;
    }

    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() == node);
      this.VisitRequires(node.Requires);
      this.VisitExpr(node.Expr);
      return node;
    }
  }
}