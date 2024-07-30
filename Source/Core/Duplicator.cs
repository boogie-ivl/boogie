using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie
{
  public class Duplicator : StandardVisitor
  {
    // This is used to ensure that Procedures get duplicated only once
    // and that Implementation.Proc is resolved to the correct duplicated
    // Procedure.
    private Dictionary<Procedure, Procedure> OldToNewProcedureMap = null;

    public override Absy Visit(Absy node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      node = base.Visit(node);
      return node;
    }

    public override Cmd VisitAssertCmd(AssertCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitAssertCmd((AssertCmd) node.Clone());
    }

    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitAssertEnsuresCmd((AssertEnsuresCmd) node.Clone());
    }

    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitAssertRequiresCmd((AssertRequiresCmd) node.Clone());
    }

    public override Cmd VisitAssignCmd(AssignCmd node)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);
      AssignCmd clone = (AssignCmd) node.Clone();
      clone.Lhss = new List<AssignLhs>(clone.Lhss);
      clone.Rhss = new List<Expr>(clone.Rhss);
      return base.VisitAssignCmd(clone);
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node)
    {
      return base.VisitUnpackCmd((UnpackCmd) node.Clone());
    }
    
    public override Cmd VisitAssumeCmd(AssumeCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitAssumeCmd((AssumeCmd) node.Clone());
    }

    public override AtomicRE VisitAtomicRE(AtomicRE node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AtomicRE>() != null);
      return base.VisitAtomicRE((AtomicRE) node.Clone());
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Axiom>() != null);
      return base.VisitAxiom((Axiom) node.Clone());
    }

    public override Type VisitBasicType(BasicType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // do /not/ clone the type recursively
      return (BasicType) node.Clone();
    }

    public override Block VisitBlock(Block node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Block>() != null);
      return base.VisitBlock((Block) node.Clone());
    }

    public override Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitBvConcatExpr((BvConcatExpr) node.Clone());
    }

    public override Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitBvExtractExpr((BvExtractExpr) node.Clone());
    }

    public override Expr VisitCodeExpr(CodeExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      CodeExpr clone = (CodeExpr) base.VisitCodeExpr((CodeExpr) node.Clone());
      // Before returning, fix up the resolved goto targets
      Contract.Assert(node.Blocks.Count == clone.Blocks.Count);
      Dictionary<Block, Block> subst = new Dictionary<Block, Block>();
      for (int i = 0; i < node.Blocks.Count; i++)
      {
        subst.Add(node.Blocks[i], clone.Blocks[i]);
      }

      foreach (Block /*!*/ b in clone.Blocks)
      {
        Contract.Assert(b != null);
        GotoCmd g = b.TransferCmd as GotoCmd;
        if (g != null)
        {
          List<Block> targets = new List<Block>();
          foreach (Block t in cce.NonNull(g.labelTargets))
          {
            Block nt = subst[t];
            targets.Add(nt);
          }

          g.labelTargets = targets;
        }
      }

      return clone;
    }

    public override List<Block> VisitBlockSeq(List<Block> blockSeq)
    {
      //Contract.Requires(blockSeq != null);
      Contract.Ensures(Contract.Result<List<Block>>() != null);
      return base.VisitBlockSeq(new List<Block>(blockSeq));
    }

    public override List<Block /*!*/> /*!*/ VisitBlockList(List<Block /*!*/> /*!*/ blocks)
    {
      //Contract.Requires(cce.NonNullElements(blocks));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
      return base.VisitBlockList(new List<Block /*!*/>(blocks));
    }

    public override BoundVariable VisitBoundVariable(BoundVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BoundVariable>() != null);
      return base.VisitBoundVariable((BoundVariable) node.Clone());
    }

    public override Type VisitBvType(BvType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // do /not/ clone the type recursively
      return (BvType) node.Clone();
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      CallCmd clone = (CallCmd) node.Clone();
      Contract.Assert(clone != null);
      clone.Ins = new List<Expr>(clone.Ins);
      clone.Outs = new List<IdentifierExpr>(clone.Outs);
      return base.VisitCallCmd(clone);
    }

    public override Choice VisitChoice(Choice node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Choice>() != null);
      return base.VisitChoice((Choice) node.Clone());
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      //Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      return base.VisitCmdSeq(new List<Cmd>(cmdSeq));
    }

    public override List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds)
    {
      return base.VisitCallCmdSeq(new List<CallCmd>(callCmds));
    }

    public override List<AssertCmd> VisitAssertCmdSeq(List<AssertCmd> assertCmds)
    {
      return base.VisitAssertCmdSeq(new List<AssertCmd>(assertCmds));
    }

    public override Constant VisitConstant(Constant node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Constant>() != null);
      return base.VisitConstant((Constant) node.Clone());
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<CtorType>() != null);
      // do /not/ clone the type recursively
      return (CtorType) node.Clone();
    }

    public override Declaration VisitDeclaration(Declaration node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Declaration>() != null);
      return base.VisitDeclaration((Declaration) node.Clone());
    }

    public override List<Declaration /*!*/> /*!*/ VisitDeclarationList(List<Declaration /*!*/> /*!*/ declarationList)
    {
      //Contract.Requires(cce.NonNullElements(declarationList));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Declaration>>()));

      // For Implementation.Proc to resolve correctly to duplicated Procedures
      // we need to visit the procedures first
      for (int i = 0, n = declarationList.Count; i < n; i++)
      {
        if (!(declarationList[i] is Procedure))
        {
          continue;
        }

        declarationList[i] = cce.NonNull((Declaration) this.Visit(declarationList[i]));
      }

      // Now visit everything else
      for (int i = 0, n = declarationList.Count; i < n; i++)
      {
        if (declarationList[i] is Procedure)
        {
          continue;
        }

        declarationList[i] = cce.NonNull((Declaration) this.Visit(declarationList[i]));
      }

      return declarationList;
    }

    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<DeclWithFormals>() != null);
      return base.VisitDeclWithFormals((DeclWithFormals) node.Clone());
    }

    public override Ensures VisitEnsures(Ensures node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Ensures>() != null);
      return base.VisitEnsures((Ensures) node.Clone());
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
    {
      //Contract.Requires(ensuresSeq != null);
      Contract.Ensures(Contract.Result<List<Ensures>>() != null);
      return base.VisitEnsuresSeq(new List<Ensures>(ensuresSeq));
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitExistsExpr((ExistsExpr) node.Clone());
    }

    public override Expr VisitExpr(Expr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitExpr((Expr) node.Clone());
    }

    public override IList<Expr> VisitExprSeq(IList<Expr> list)
    {
      //Contract.Requires(list != null);
      Contract.Ensures(Contract.Result<IList<Expr>>() != null);
      return base.VisitExprSeq(new List<Expr>(list));
    }

    public override Type VisitFloatType(FloatType node)
    {
      return (FloatType) node.Clone();
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitForallExpr((ForallExpr) node.Clone());
    }

    public override Formal VisitFormal(Formal node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Formal>() != null);
      return base.VisitFormal((Formal) node.Clone());
    }

    public override Function VisitFunction(Function node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Function>() != null);
      return base.VisitFunction((Function) node.Clone());
    }

    public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GlobalVariable>() != null);
      return base.VisitGlobalVariable((GlobalVariable) node.Clone());
    }

    public override GotoCmd VisitGotoCmd(GotoCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<GotoCmd>() != null);
      // NOTE: This doesn't duplicate the labelTarget basic blocks
      // or resolve them to the new blocks
      // VisitImplementation() and VisitBlock() handle this
      return base.VisitGotoCmd((GotoCmd) node.Clone());
    }

    public override Cmd VisitHavocCmd(HavocCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitHavocCmd((HavocCmd) node.Clone());
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitIdentifierExpr((IdentifierExpr) node.Clone());
    }

    public override List<IdentifierExpr> VisitIdentifierExprSeq(List<IdentifierExpr> identifierExprSeq)
    {
      //Contract.Requires(identifierExprSeq != null);
      Contract.Ensures(Contract.Result<List<IdentifierExpr>>() != null);
      return base.VisitIdentifierExprSeq(new List<IdentifierExpr>(identifierExprSeq));
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Implementation>() != null);
      var impl = base.VisitImplementation((Implementation) node.Clone());
      var blockDuplicationMapping = new Dictionary<Block, Block>();

      // Compute the mapping between the blocks of the old implementation (node)
      // and the new implementation (impl).
      foreach (var blockPair in node.Blocks.Zip(impl.Blocks))
      {
        blockDuplicationMapping.Add(blockPair.Item1, blockPair.Item2);
      }

      // The GotoCmds and blocks have now been duplicated.
      // Resolve GotoCmd targets to the duplicated blocks
      foreach (GotoCmd gotoCmd in impl.Blocks.Select(bb => bb.TransferCmd).OfType<GotoCmd>())
      {
        var newLabelTargets = new List<Block>();
        var newLabelNames = new List<string>();
        for (int index = 0; index < gotoCmd.labelTargets.Count; ++index)
        {
          var newBlock = blockDuplicationMapping[gotoCmd.labelTargets[index]];
          newLabelTargets.Add(newBlock);
          newLabelNames.Add(newBlock.Label);
        }

        gotoCmd.labelTargets = newLabelTargets;
        gotoCmd.labelNames = newLabelNames;
      }

      if (impl.Proc is YieldProcedureDecl yieldProcedureDecl)
      {
        var newYieldingLoops = new Dictionary<Block, YieldingLoop>();
        foreach (var kv in yieldProcedureDecl.YieldingLoops)
        {
          newYieldingLoops[blockDuplicationMapping[kv.Key]] = kv.Value;
        }
        yieldProcedureDecl.YieldingLoops = newYieldingLoops;
      }

      return impl;
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitLetExpr((LetExpr) node.Clone());
    }

    public override Expr VisitLiteralExpr(LiteralExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitLiteralExpr((LiteralExpr) node.Clone());
    }

    public override LocalVariable VisitLocalVariable(LocalVariable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<LocalVariable>() != null);
      return base.VisitLocalVariable((LocalVariable) node.Clone());
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      MapAssignLhs clone = (MapAssignLhs) node.Clone();
      clone.Indexes = new List<Expr /*!*/>(clone.Indexes);
      return base.VisitMapAssignLhs(clone);
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      FieldAssignLhs clone = (FieldAssignLhs) node.Clone();
      return base.VisitFieldAssignLhs(clone);
    }

    public override Type VisitMapType(MapType node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<MapType>() != null);
      // do /not/ clone the type recursively
      return (MapType) node.Clone();
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitNAryExpr((NAryExpr) node.Clone());
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return base.VisitOldExpr((OldExpr) node.Clone());
    }

    public override Cmd VisitParCallCmd(ParCallCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      ParCallCmd clone = (ParCallCmd) node.Clone();
      Contract.Assert(clone != null);
      clone.CallCmds = new List<CallCmd>(node.CallCmds);
      return base.VisitParCallCmd(clone);
    }

    public override Procedure VisitProcedure(Procedure node)
    {
      Procedure newProcedure = null;
      if (OldToNewProcedureMap != null && OldToNewProcedureMap.ContainsKey(node))
      {
        newProcedure = OldToNewProcedureMap[node];
      }
      else
      {
        newProcedure = base.VisitProcedure((Procedure) node.Clone());
        if (OldToNewProcedureMap != null)
        {
          OldToNewProcedureMap[node] = newProcedure;
        }
      }
      return newProcedure;
    }

    // We duplicate ActionDecl's but we are not updating references to ActionDecl
    // in ActionDeclRef instances. If ActionDeclRef instances need to be updated,
    // override VisitActionDeclRef appropriately.
    public override Procedure VisitActionDecl(ActionDecl node)
    {
      Procedure newProcedure = null;
      if (OldToNewProcedureMap != null && OldToNewProcedureMap.ContainsKey(node))
      {
        newProcedure = OldToNewProcedureMap[node];
      }
      else
      {
        newProcedure = base.VisitActionDecl((ActionDecl) node.Clone());
        if (OldToNewProcedureMap != null)
        {
          OldToNewProcedureMap[node] = newProcedure;
        }
      }
      return newProcedure;
    }

    public override HashSet<Variable> VisitVariableSet(HashSet<Variable> node)
    {
      return base.VisitVariableSet(new HashSet<Variable>(node));
    }

    public override YieldingLoop VisitYieldingLoop(YieldingLoop node)
    {
      return base.VisitYieldingLoop(new YieldingLoop(node.Layer, node.YieldInvariants));
    }

    public override Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node)
    {
      return base.VisitYieldingLoops(new Dictionary<Block, YieldingLoop>(node));
    }

    public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
    {
      Procedure newProcedure = null;
      if (OldToNewProcedureMap != null && OldToNewProcedureMap.ContainsKey(node))
      {
        newProcedure = OldToNewProcedureMap[node];
      }
      else
      {
        newProcedure = base.VisitYieldProcedureDecl((YieldProcedureDecl) node.Clone());
        if (OldToNewProcedureMap != null)
        {
          OldToNewProcedureMap[node] = newProcedure;
        }
      }
      return newProcedure;
    }

    public override Program VisitProgram(Program node)
    {
      // If cloning an entire program we need to ensure that
      // Implementation.Proc gets resolved to the right Procedure
      // (i.e. we don't duplicate Procedure twice) and CallCmds
      // call the right Procedure.
      // The map below is used to achieve this.
      OldToNewProcedureMap = new Dictionary<Procedure, Procedure>();
      var newProgram = base.VisitProgram((Program) node.Clone());

      // We need to make sure that CallCmds get resolved to call Procedures we duplicated
      // instead of pointing to procedures in the old program
      var callCmds = newProgram.Blocks().SelectMany(b => b.Cmds).OfType<CallCmd>();
      var yieldCallCmds = newProgram.TopLevelDeclarations.OfType<YieldProcedureDecl>()
        .SelectMany(decl => decl.CallCmds());
      foreach (var callCmd in callCmds.Union(yieldCallCmds))
      {
        callCmd.Proc = OldToNewProcedureMap[callCmd.Proc];
      }

      // We need to make sure that ActionDeclRefs are resolved to the new ActionDecls.
      var actionDeclRefsInActionDecls = newProgram.TopLevelDeclarations.OfType<ActionDecl>()
        .SelectMany(decl => decl.ActionDeclRefs());
      var actionDeclRefsInYieldProcedureDecls = newProgram.TopLevelDeclarations.OfType<YieldProcedureDecl>()
        .Select(decl => decl.RefinedAction);
      foreach (var actionDeclRef in actionDeclRefsInActionDecls.Union(actionDeclRefsInYieldProcedureDecls))
      {
        actionDeclRef.ActionDecl = (ActionDecl)OldToNewProcedureMap[actionDeclRef.ActionDecl];
      }

      OldToNewProcedureMap = null; // This Visitor could be used for other things later so remove the map.
      return newProgram;
    }

    public override QKeyValue VisitQKeyValue(QKeyValue node)
    {
      //Contract.Requires(node != null);
      var newParams = new List<object>();
      foreach (var o in node.Params)
      {
        var e = o as Expr;
        if (e == null)
        {
          newParams.Add(o);
        }
        else
        {
          newParams.Add((Expr) this.Visit(e));
        }
      }

      QKeyValue next = node.Next == null ? null : (QKeyValue) this.Visit(node.Next);
      return new QKeyValue(node.tok, node.Key, newParams, next);
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<BinderExpr>() != null);
      return base.VisitBinderExpr((BinderExpr) node.Clone());
    }

    public override Requires VisitRequires(Requires node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Requires>() != null);
      return base.VisitRequires((Requires) node.Clone());
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
    {
      //Contract.Requires(requiresSeq != null);
      Contract.Ensures(Contract.Result<List<Requires>>() != null);
      return base.VisitRequiresSeq(new List<Requires>(requiresSeq));
    }

    public override Cmd VisitRE(RE node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitRE((RE) node.Clone());
    }

    public override List<RE> VisitRESeq(List<RE> reSeq)
    {
      //Contract.Requires(reSeq != null);
      Contract.Ensures(Contract.Result<List<RE>>() != null);
      return base.VisitRESeq(new List<RE>(reSeq));
    }

    public override ReturnCmd VisitReturnCmd(ReturnCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnCmd>() != null);
      return base.VisitReturnCmd((ReturnCmd) node.Clone());
    }

    public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<ReturnExprCmd>() != null);
      return base.VisitReturnExprCmd((ReturnExprCmd) node.Clone());
    }

    public override Sequential VisitSequential(Sequential node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Sequential>() != null);
      return base.VisitSequential((Sequential) node.Clone());
    }

    public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      return base.VisitSimpleAssignLhs((SimpleAssignLhs) node.Clone());
    }

    public override Cmd VisitStateCmd(StateCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return base.VisitStateCmd((StateCmd) node.Clone());
    }

    public override TransferCmd VisitTransferCmd(TransferCmd node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TransferCmd>() != null);
      return base.VisitTransferCmd((TransferCmd) node.Clone());
    }

    public override Trigger VisitTrigger(Trigger node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Trigger>() != null);
      return base.VisitTrigger((Trigger) node.Clone());
    }

    public override Type VisitType(Type node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      // do /not/ clone the type recursively
      return (Type) node.Clone();
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<TypedIdent>() != null);
      return base.VisitTypedIdent((TypedIdent) node.Clone());
    }

    public override Variable VisitVariable(Variable node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      return node;
    }

    public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
    {
      //Contract.Requires(variableSeq != null);
      Contract.Ensures(Contract.Result<List<Variable>>() != null);
      return base.VisitVariableSeq(new List<Variable>(variableSeq));
    }
  }


  #region A duplicator that also does substitutions for a set of variables

  /// <summary>
  /// A substitution is a partial mapping from Variables to Exprs.
  /// </summary>
  public delegate Expr /*?*/ Substitution(Variable /*!*/ v);

  public static class Substituter
  {
    public static Substitution SubstitutionFromDictionary(Dictionary<Variable, Expr> map, bool fallBackOnName = false,
      Procedure proc = null)
    {
      Contract.Requires(map != null);
      Contract.Ensures(Contract.Result<Substitution>() != null);
      // TODO: With Whidbey, could use anonymous functions.
      return new Substitution(new CreateSubstitutionClosure(map, fallBackOnName, proc).Method);
    }

    private sealed class CreateSubstitutionClosure
    {
      Dictionary<Variable /*!*/, Expr /*!*/> /*!*/
        map;

      Dictionary<string /*!*/, Expr /*!*/> /*!*/
        nameMap;

      Procedure proc;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(map != null);
      }

      static string UniqueName(Variable variable, Procedure proc)
      {
        // TODO(wuestholz): Maybe we should define structural equality for variables instead.
        var scope = "#global_scope#";
        if (proc != null && !(variable is GlobalVariable || variable is Constant))
        {
          scope = proc.Name;
        }

        return string.Format("{0}.{1}", scope, variable.Name);
      }

      public CreateSubstitutionClosure(Dictionary<Variable, Expr> map, bool fallBackOnName = false,
        Procedure proc = null)
        : base()
      {
        Contract.Requires(map != null);
        this.map = map;
        this.proc = proc;
        if (fallBackOnName && proc != null)
        {
          this.nameMap = map.ToDictionary(kv => UniqueName(kv.Key, proc), kv => kv.Value);
        }
      }

      public Expr /*?*/ Method(Variable v)
      {
        Contract.Requires(v != null);
        if (map.ContainsKey(v))
        {
          return map[v];
        }

        if (nameMap != null && proc != null && nameMap.TryGetValue(UniqueName(v, proc), out var e))
        {
          return e;
        }

        return null;
      }
    }

    // ----------------------------- Substitutions for Expr -------------------------------

    /// <summary>
    /// Apply a substitution to an expression.  Any variables not in domain(subst)
    /// is not changed.  The substitutions apply within the "old", but the "old"
    /// expression remains.
    /// </summary>
    public static Expr Apply(Substitution subst, Expr expr)
    {
      Contract.Requires(subst != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr) new NormalSubstituter(subst).Visit(expr);
    }

    /// <summary>
    /// Apply a substitution to an expression. 
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>
    public static Expr Apply(Substitution always, Substitution forold, Expr expr)
    {
      Contract.Requires(always != null);
      Contract.Requires(forold != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr) new NormalSubstituter(always, forold).Visit(expr);
    }

    /// <summary>
    /// Apply a substitution to an expression replacing "old" expressions.
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>    
    public static Expr ApplyReplacingOldExprs(Substitution always, Substitution forOld, Expr expr)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr) new ReplacingOldSubstituter(always, forOld).Visit(expr);
    }

    public static Expr FunctionCallReresolvingApplyReplacingOldExprs(Substitution always, Substitution forOld,
      Expr expr, Program program)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr) new FunctionCallReresolvingReplacingOldSubstituter(program, always, forOld).Visit(expr);
    }

    public static Expr FunctionCallReresolvingApply(Substitution always, Substitution forOld, Expr expr,
      Program program)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      return (Expr) new FunctionCallReresolvingNormalSubstituter(program, always, forOld).Visit(expr);
    }

    // ----------------------------- Substitutions for Cmd -------------------------------

    /// <summary>
    /// Apply a substitution to a command.  Any variables not in domain(subst)
    /// is not changed.  The substitutions apply within the "old", but the "old"
    /// expression remains.
    /// </summary>
    public static Cmd Apply(Substitution subst, Cmd cmd)
    {
      Contract.Requires(subst != null);
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd) new NormalSubstituter(subst).Visit(cmd);
    }

    /// <summary>
    /// Apply a substitution to a command.  
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>
    public static Cmd Apply(Substitution always, Substitution forOld, Cmd cmd)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd) new NormalSubstituter(always, forOld).Visit(cmd);
    }

    /// <summary>
    /// Apply a substitution to a command replacing "old" expressions.
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>    
    public static Cmd ApplyReplacingOldExprs(Substitution always, Substitution forOld, Cmd cmd)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(cmd != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return (Cmd) new ReplacingOldSubstituter(always, forOld).Visit(cmd);
    }

    // ----------------------------- Substitutions for CmdSeq -------------------------------

    /// <summary>
    /// Apply a substitution to a command sequence.  Any variables not in domain(subst)
    /// is not changed.  The substitutions apply within the "old", but the "old"
    /// expression remains.
    /// </summary>
    public static List<Cmd> Apply(Substitution subst, List<Cmd> cmdSeq)
    {
      Contract.Requires(subst != null);
      Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return new NormalSubstituter(subst).VisitCmdSeq(cmdSeq);
    }

    /// <summary>
    /// Apply a substitution to a command sequence.  
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>
    public static List<Cmd> Apply(Substitution always, Substitution forOld, List<Cmd> cmdSeq)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return new NormalSubstituter(always, forOld).VisitCmdSeq(cmdSeq);
    }

    /// <summary>
    /// Apply a substitution to a command sequence replacing "old" expressions.
    /// Outside "old" expressions, the substitution "always" is applied; any variable not in
    /// domain(always) is not changed.  Inside "old" expressions, apply map "forOld" to
    /// variables in domain(forOld), apply map "always" to variables in
    /// domain(always)-domain(forOld), and leave variable unchanged otherwise.
    /// </summary>    
    public static List<Cmd> ApplyReplacingOldExprs(Substitution always, Substitution forOld, List<Cmd> cmdSeq)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      Contract.Requires(cmdSeq != null);
      Contract.Ensures(Contract.Result<Cmd>() != null);
      return new ReplacingOldSubstituter(always, forOld).VisitCmdSeq(cmdSeq);
    }
    
    // ----------------------------- Substitutions for QKeyValue -------------------------------

    /// <summary>
    /// Apply a substitution to a list of attributes.  Any variables not in domain(subst)
    /// is not changed.  The substitutions apply within the "old", but the "old"
    /// expression remains.
    /// </summary>
    public static QKeyValue Apply(Substitution subst, QKeyValue kv)
    {
      Contract.Requires(subst != null);
      if (kv == null)
      {
        return null;
      }
      else
      {
        return (QKeyValue) new NormalSubstituter(subst).Visit(kv);
      }
    }

    /// <summary>
    /// Apply a substitution to a list of attributes replacing "old" expressions.
    /// For a further description, see "ApplyReplacingOldExprs" above for Expr.
    /// </summary>    
    public static QKeyValue ApplyReplacingOldExprs(Substitution always, Substitution forOld, QKeyValue kv)
    {
      Contract.Requires(always != null);
      Contract.Requires(forOld != null);
      if (kv == null)
      {
        return null;
      }
      else
      {
        return (QKeyValue) new ReplacingOldSubstituter(always, forOld).Visit(kv);
      }
    }

    // ------------------------------------------------------------

    private class NormalSubstituter : Duplicator
    {
      private readonly Substitution /*!*/
        always;

      private readonly Substitution /*!*/
        forold;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(always != null);
        Contract.Invariant(forold != null);
      }

      public NormalSubstituter(Substitution subst)
        : base()
      {
        Contract.Requires(subst != null);
        this.always = subst;
        this.forold = Substituter.SubstitutionFromDictionary(new Dictionary<Variable, Expr>());
      }

      public NormalSubstituter(Substitution subst, Substitution forold)
        : base()
      {
        Contract.Requires(subst != null);
        this.always = subst;
        this.forold = forold;
      }

      private bool insideOldExpr = false;

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        Expr /*?*/
          e = null;

        if (insideOldExpr)
        {
          e = forold(cce.NonNull(node.Decl));
        }

        if (e == null)
        {
          e = always(cce.NonNull(node.Decl));
        }

        return e == null ? base.VisitIdentifierExpr(node) : e;
      }

      public override Expr VisitOldExpr(OldExpr node)
      {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        bool previouslyInOld = insideOldExpr;
        insideOldExpr = true;
        Expr /*!*/
          e = (Expr /*!*/) cce.NonNull(this.Visit(node.Expr));
        insideOldExpr = previouslyInOld;
        return new OldExpr(node.tok, e);
      }
    }

    private sealed class FunctionCallReresolvingReplacingOldSubstituter : ReplacingOldSubstituter
    {
      readonly Program Program;

      public FunctionCallReresolvingReplacingOldSubstituter(Program program, Substitution always, Substitution forold)
        : base(always, forold)
      {
        Program = program;
      }

      public override Expr VisitNAryExpr(NAryExpr node)
      {
        var result = base.VisitNAryExpr(node);
        var nAryExpr = result as NAryExpr;
        if (nAryExpr != null)
        {
          var funCall = nAryExpr.Fun as FunctionCall;
          if (funCall != null)
          {
            funCall.Func = Program.FindFunction(funCall.FunctionName);
          }
        }

        return result;
      }
    }

    private sealed class FunctionCallReresolvingNormalSubstituter : NormalSubstituter
    {
      readonly Program Program;

      public FunctionCallReresolvingNormalSubstituter(Program program, Substitution always, Substitution forold)
        : base(always, forold)
      {
        Program = program;
      }

      public override Expr VisitNAryExpr(NAryExpr node)
      {
        var result = base.VisitNAryExpr(node);
        var nAryExpr = result as NAryExpr;
        if (nAryExpr != null)
        {
          var funCall = nAryExpr.Fun as FunctionCall;
          if (funCall != null)
          {
            funCall.Func = Program.FindFunction(funCall.FunctionName);
          }
        }

        return result;
      }
    }

    private class ReplacingOldSubstituter : Duplicator
    {
      private readonly Substitution /*!*/
        always;

      private readonly Substitution /*!*/
        forold;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(always != null);
        Contract.Invariant(forold != null);
      }

      public ReplacingOldSubstituter(Substitution always, Substitution forold)
        : base()
      {
        Contract.Requires(forold != null);
        Contract.Requires(always != null);
        this.always = always;
        this.forold = forold;
      }

      private bool insideOldExpr = false;

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        Expr /*?*/
          e = null;

        if (insideOldExpr)
        {
          e = forold(cce.NonNull(node.Decl));
        }

        if (e == null)
        {
          e = always(cce.NonNull(node.Decl));
        }

        return e == null ? base.VisitIdentifierExpr(node) : e;
      }

      public override Expr VisitOldExpr(OldExpr node)
      {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Expr>() != null);
        bool previouslyInOld = insideOldExpr;
        insideOldExpr = true;
        Expr /*!*/
          e = (Expr /*!*/) cce.NonNull(this.Visit(node.Expr));
        insideOldExpr = previouslyInOld;
        return e;
      }
    }
  }

  class BoundVarAndReplacingOldSubstituter : Duplicator
  {
    private Dictionary<Variable, Expr> subst;
    private Dictionary<Variable, Expr> oldSubst;
    private readonly string prefix;
    private Dictionary<Variable, Expr> boundVarSubst;
    private int insideOldExpr;

    public static Expr Apply(Dictionary<Variable, Expr> subst, Dictionary<Variable, Expr> oldSubst, string prefix, Expr expr)
    {
      return (Expr) new BoundVarAndReplacingOldSubstituter(subst, oldSubst, prefix).Visit(expr);
    }
    
    public static Cmd Apply(Dictionary<Variable, Expr> subst, Dictionary<Variable, Expr> oldSubst, string prefix, Cmd cmd)
    {
      return (Cmd) new BoundVarAndReplacingOldSubstituter(subst, oldSubst, prefix).Visit(cmd);
    }
    
    private BoundVarAndReplacingOldSubstituter(Dictionary<Variable, Expr> subst, Dictionary<Variable, Expr> oldSubst, string prefix)
    {
      this.subst = subst;
      this.oldSubst = oldSubst;
      this.prefix = prefix;
      this.boundVarSubst = new Dictionary<Variable, Expr>();
      this.insideOldExpr = 0;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (0 < insideOldExpr && oldSubst.ContainsKey(node.Decl))
      {
        return oldSubst[node.Decl];
      }
      if (subst.ContainsKey(node.Decl))
      { 
        return subst[node.Decl];
      }
      if (boundVarSubst.ContainsKey(node.Decl))
      {
        return boundVarSubst[node.Decl];
      }
      return base.VisitIdentifierExpr(node);
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      insideOldExpr++;
      Expr e = (Expr) this.Visit(node.Expr);
      insideOldExpr--;
      return e;
    }
    
    public override Expr VisitBinderExpr(BinderExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          x.Attributes));

      foreach (var x in node.Dummies)
      {
        boundVarSubst.Add(x, Expr.Ident(oldToNew[x]));
      }

      BinderExpr expr = (BinderExpr)base.VisitBinderExpr(node);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

      // We process triggers of quantifier expressions here, because otherwise the
      // substitutions for bound variables have to be leaked outside this procedure.
      if (node is QuantifierExpr quantifierExpr)
      {
        if (quantifierExpr.Triggers != null)
        {
          ((QuantifierExpr) expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
        }
      }

      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }

      return expr;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
      return (QuantifierExpr) this.VisitBinderExpr(node);
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type),
          x.Attributes));

      foreach (var x in node.Dummies)
      {
        boundVarSubst.Add(x, Expr.Ident(oldToNew[x]));
      }

      var expr = (LetExpr) base.VisitLetExpr(node);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }

      return expr;
    }
  }
  #endregion
}