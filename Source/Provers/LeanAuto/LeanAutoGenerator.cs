using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Boogie.LeanAuto;

internal class LeanConversionException : Exception
{
  public string Msg { get; }
  public LeanConversionException(IToken tok, string s)
  {
    Msg = tok + ": " + s;
  }
}

public class LeanAutoGenerator : ReadOnlyVisitor
{
  private readonly TextWriter writer;
  private readonly VCGenOptions options;
  private readonly List<NamedDeclaration> globalVars = new();
  private readonly HashSet<string> usedNames = new();
  private bool usesMaps;
  private readonly List<string> mapAxiomNames =
    new(new[]
    {
      "SelectStoreSame1", "SelectStoreDistinct1",
      "SelectStoreSame2", "SelectStoreDistinct2"
    });
  private readonly List<string> userAxiomNames = new();
  private readonly Dictionary<Type, HashSet<string>> uniqueConsts = new();

  private const string AndString = "\u2227"; /* ∧ */
  private const string OrString = "\u2228"; /* ∨ */
  private const string NeqString = "\u2260"; /* ≠ */
  private const string ArrowString = "\u2192"; /* → */

  private LeanAutoGenerator(VCGenOptions options, TextWriter writer)
  {
    this.options = options;
    this.writer = writer;
  }

  public static void EmitPassiveProgramAsLean(VCGenOptions options, Program p, TextWriter writer)
  {
    var generator = new LeanAutoGenerator(options, writer);
    generator.EmitHeader();
    try {
      var allBlocks = p.Implementations.SelectMany(i => i.Blocks);
      var liveDeclarations =
        !options.Prune
          ? p.TopLevelDeclarations
          : Pruner.GetLiveDeclarations(options, p, allBlocks.ToList()).ToList();

      generator.WriteLine("-- Type constructors");
      // Always include all type constructors
      p.TopLevelDeclarations.OfType<TypeCtorDecl>().ForEach(tcd => generator.Visit(tcd));
      generator.WriteLine();

      generator.WriteLine("-- Type synonyms");
      liveDeclarations.OfType<TypeSynonymDecl>().ForEach(tcd => generator.Visit(tcd));
      generator.WriteLine();

      generator.WriteLine("-- Constants");
      liveDeclarations.OfType<Constant>().ForEach(c => generator.Visit(c));
      generator.WriteLine();

      generator.WriteLine("-- Unique const axioms");
      generator.EmitUniqueConstAxioms();
      generator.WriteLine();

      generator.WriteLine("-- Variables");
      liveDeclarations.OfType<GlobalVariable>().ForEach(gv => generator.Visit(gv));
      generator.WriteLine();

      generator.WriteLine("-- Functions");
      liveDeclarations.OfType<Function>().ForEach(f => generator.Visit(f));
      generator.WriteLine();

      generator.WriteLine("-- Axioms");
      liveDeclarations.OfType<Axiom>().ForEach(a => generator.Visit(a));
      generator.WriteLine();

      generator.WriteLine("-- Implementations");
      p.Implementations.ForEach(i => generator.Visit(i));
    } catch (LeanConversionException e) {
      Console.WriteLine($"Failed translation: {e.Msg}");
      Environment.Exit(1);
    }
  }

  private void AddUniqueConst(Type t, string name)
  {
    if (!uniqueConsts.ContainsKey(t)) {
      uniqueConsts[t] = new();
    }
    if (!uniqueConsts[t].Contains(name)) {
      uniqueConsts[t].Add(name);
    }
  }

  private void EmitUniqueConstAxioms()
  {
    int i = 0;
    foreach (var kv in uniqueConsts) {
      var axiomName = $"unique{i}";
      userAxiomNames.Add(axiomName);
      WriteText($"axiom {axiomName}: distinct ");
      WriteList(kv.Value);
      WriteLine();
      i++;
    }
  }

  private void EmitHeader()
  {
    var assembly = System.Reflection.Assembly.GetExecutingAssembly();
    var preludeStream = assembly.GetManifestResourceStream("Prelude.lean");
    if (preludeStream is null) {
      throw new LeanConversionException(Token.NoToken,
        "Internal: failed to find Lean prelude in assembly.");
    }
    var header = new StreamReader(preludeStream).ReadToEnd();
    writer.WriteLine(header.ReplaceLineEndings());
  }

  private void Indent(int n = 1, string str = null)
  {
    WriteText(String.Concat(Enumerable.Repeat("  ", n)));

    if (str is not null) {
      WriteText(str);
    }
  }

  private void IndentLine(int n = 1, string str = null)
  {
    Indent(n, str);
    WriteLine();
  }

  private void WriteLine()
  {
    writer.WriteLine();
  }

  private void WriteText(string text)
  {
    writer.Write(text);
  }

  private void WriteLine(string text)
  {
    writer.WriteLine(text);
  }

  private void WriteList(IEnumerable<string> strings)
  {
    WriteText("[");
    WriteText(String.Join(", ", strings));
    WriteText("]");
  }

  public override Block VisitBlock(Block node)
  {
    var label = BlockName(node);
    IndentLine(1, "@[simp]");
    IndentLine(1, $"{label} :=");
    node.Cmds.ForEach(c => Visit(c));
    if (node.TransferCmd is ReturnCmd r) {
      VisitReturnCmd(r);
    } else if (node.TransferCmd is GotoCmd g) {
      VisitGotoCmd(g);
    } else {
      throw new LeanConversionException(node.TransferCmd.tok,
        $"Unsupported transfer command: {node.TransferCmd}");
    }
    WriteLine();
    return node;
  }

  public override Cmd VisitAssertCmd(AssertCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    WriteLine(" $");
    return node;
  }

  public override Cmd VisitAssumeCmd(AssumeCmd node)
  {
    Indent(2, "assume ");
    VisitExpr(node.Expr);
    WriteLine(" $");
    return node;
  }

  public override GotoCmd VisitGotoCmd(GotoCmd node)
  {
    string cmd = node.labelTargets.Any()
      ? node
        .labelTargets
        .Select(l => $"goto {BlockName(l)}")
        .Aggregate((a, b) => $"{a} {AndString} {b}")
      : "ret";
    Indent(2, cmd);
    return node;
  }

  public override ReturnCmd VisitReturnCmd(ReturnCmd node)
  {
    Indent(2, "ret");
    return node;
  }

  public override Expr VisitIdentifierExpr(IdentifierExpr node)
  {
    var name = SanitizeNameForLean(node.Name);
    usedNames.Add(name);
    WriteText(name);
    return node;
  }

  public override Type VisitType(Type node)
  {
    return node switch
    {
      BasicType basicType => VisitBasicType(basicType),
      BvType bvType => VisitBvType(bvType),
      CtorType ctorType => VisitCtorType(ctorType),
      FloatType floatType => VisitFloatType(floatType),
      MapType mapType => VisitMapType(mapType),
      TypeProxy typeProxy => VisitTypeProxy(typeProxy),
      TypeSynonymAnnotation typeSynonymAnnotation =>
        VisitTypeSynonymAnnotation(typeSynonymAnnotation),
      TypeVariable typeVariable => VisitTypeVariable(typeVariable),
      UnresolvedTypeIdentifier uti => VisitUnresolvedTypeIdentifier(uti),
      _ => throw new LeanConversionException(node.tok,
        $"Internal: Branch should be unreachable for Type: {node}.")
    };
  }

  public override Type VisitBasicType(BasicType node)
  {
    if (node.IsBool) {
      WriteText("Prop");
    } else if (node.IsInt) {
      WriteText("Int");
    } else if (node.IsReal) {
      WriteText("Real");
    } else if (node.IsRMode) {
      throw new LeanConversionException(node.tok, "Unsupported type: RMode.");
    } else if (node.IsRegEx) {
      throw new LeanConversionException(node.tok, "Unsupported type: RegEx.");
    } else if (node.IsString) {
      throw new LeanConversionException(node.tok, "Unsupported type: String.");
    } else {
      throw new LeanConversionException(node.tok,
        $"Internal: Branch should be unreachable for BasicType: {node}.");
    }

    return node;
  }

  public override Expr VisitBvConcatExpr(BvConcatExpr node)
  {
    Visit(node.E0);
    WriteText(" ++ ");
    Visit(node.E1);
    return node;
  }

  public override Type VisitBvType(BvType node)
  {
    WriteText($"(BitVec {node.Bits})");
    return node;
  }

  public override Constant VisitConstant(Constant node)
  {
    var ti = node.TypedIdent;
    WriteText("variable ");
    Visit(ti);
    if (node.Unique) {
      AddUniqueConst(ti.Type, Name(node));
    }
    WriteLine();
    globalVars.Add(node);
    return node;
  }

  public override CtorType VisitCtorType(CtorType node)
  {
    if (node.Arguments.Any()) {
      WriteText("(");
    }

    WriteText(Name(node.Decl));
    node.Arguments.ForEach(a =>
    {
      WriteText(" ");
      Visit(a);
    });
    if (node.Arguments.Any()) {
      WriteText(")");
    }
    return node;
  }

  public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
  {
    var kind = node switch
    {
      ForallExpr => "forall",
      ExistsExpr => "exists",
      _ => throw new LeanConversionException(node.tok,
        $"Unsupported quantifier type: {node.Kind}")
    };
    WriteText($"({kind}");
    foreach (var tv in node.TypeParameters) {
      WriteText($" ({Name(tv)} : Type)");
    }
    foreach (var x in node.Dummies) {
      WriteText(" ");
      VisitTypedIdent(x.TypedIdent);
    }
    WriteText(", ");
    Visit(node.Body);
    WriteText(")");

    return node;
  }

  public override TypedIdent VisitTypedIdent(TypedIdent node)
  {
    WriteText("(");
    var name = SanitizeNameForLean(node.Name);
    WriteText(name);
    WriteText(" : ");
    Visit(node.Type);
    WriteText(")");
    return node;
  }

  public override Expr VisitBvExtractExpr(BvExtractExpr node)
  {
    WriteText($"(BitVec.extractLsb {node.End - 1} {node.Start} ");
    Visit(node.Bitvector);
    WriteText(")");
    return node;
  }

  public override Expr VisitLambdaExpr(LambdaExpr node)
  {
    WriteText("(λ");
    node.Dummies.ForEach(x => Visit(x.TypedIdent));
    WriteText("=>");
    Visit(node.Body);
    WriteText(")");
    return node;
  }

  public override Expr VisitLetExpr(LetExpr node)
  {
    if (node.Dummies.Count > 1) {
      throw new LeanConversionException(node.tok,
        "Unsupported: LetExpr with more than one binder");
    }
    WriteText("(let");
    node.Dummies.ForEach(x => Visit(x.TypedIdent));
    WriteText(" := ");
    node.Rhss.ForEach(e => Visit(e));
    WriteText("; ");
    Visit(node.Body);
    WriteText(")");
    return node;
  }

  public override GlobalVariable VisitGlobalVariable(GlobalVariable node)
  {
    WriteText("variable ");
    Visit(node.TypedIdent);
    WriteLine();
    globalVars.Add(node);
    return node;
  }

  public override Expr VisitLiteralExpr(LiteralExpr node)
  {
    if(node.IsTrue) {
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      WriteText("true");
    } else if (node.IsFalse) {
      // Use lowercase version to ensure Bool, which can be coerced to Prop
      WriteText("false");
    } else if (node.isBvConst) {
      var bvConst = node.asBvConst;
      WriteText("(");
      WriteText(bvConst.Value.ToString());
      WriteText($" : BitVec {bvConst.Bits}");
      WriteText(")");
    } else if (node.isBigDec) {
      throw new LeanConversionException(node.tok,
        "Unsupported literal: BigDec");
    } else if (node.isBigNum) {
      var bigNumConst = node.asBigNum;
      WriteText(bigNumConst.ToString());
    } else if (node.isBigFloat) {
      throw new LeanConversionException(node.tok,
        "Unsupported literal: BigFloat");
    } else if (node.isRoundingMode) {
      throw new LeanConversionException(node.tok,
        "Unsupported literal: RoundingMode");
    } else {
      throw new LeanConversionException(node.tok,
        "Internal: Branch should be unreachable for literal: {node}");
    }
    return node;
  }

  public override Type VisitMapType(MapType node)
  {
    if (node.Arguments.Count > 2) {
      throw new LeanConversionException(node.tok,
        $"Unsupported: MapType with more than 2 index types ({node})");
    }
    if (node.TypeParameters.Any()) {
      var args = node.TypeParameters.Select(Name);
      WriteText($"forall ({String.Join(" ", args)} : Type), ");
    }
    WriteText($"(SMTArray{node.Arguments.Count} ");
    node.Arguments.ForEach(a =>
    {
      Visit(a);
      WriteText(" ");
    });
    Visit(node.Result);
    WriteText(")");
    return node;
  }

  public override Expr VisitNAryExpr(NAryExpr node)
  {
    var fun = node.Fun;
    var args = node.Args;
    WriteText("(");
    if (fun is BinaryOperator op && args.Count == 2) {
      Visit(args[0]);
      WriteText($" {BinaryOpToLean(op.Op)} ");
      Visit(args[1]);
    } else if (fun is FieldAccess fieldAccess) {
      throw new LeanConversionException(node.tok,
        "Unsupported: field access (since the semantics are complex)");
    } else if (fun is FieldUpdate fieldUpdate) {
      throw new LeanConversionException(node.tok,
        "Unsupported: field update (since the semantics are complex)");
    } else if (fun is IfThenElse && args.Count == 3) {
      WriteText("if ");
      Visit(args[0]);
      WriteText(" then ");
      Visit(args[1]);
      WriteText(" else ");
      Visit(args[2]);
    } else if (fun is TypeCoercion typeCoercion && args.Count == 1) {
      if (!args[0].Type.Equals(typeCoercion.Type)) {
        // TODO: might need to actually call a coercion function
        Console.WriteLine($"Coerce: {args[0].Type} -> {typeCoercion.Type}");
      }
      WriteText("(");
      Visit(args[0]);
      WriteText(" : ");
      Visit(typeCoercion.Type);
      WriteText(")");
    } else {
      VisitIAppliable(fun);
      foreach (var arg in args) {
        WriteText(" ");
        Visit(arg);
      }
    }
    WriteText(")");

    return node;
  }

  private void VisitIAppliable(IAppliable fun)
  {
    switch (fun) {
      case ArithmeticCoercion arithmeticCoercion:
        var func = arithmeticCoercion.Coercion switch
        {
          ArithmeticCoercion.CoercionType.ToInt => "realToInt",
          ArithmeticCoercion.CoercionType.ToReal => "intToReal",
          _ => throw new LeanConversionException(Token.NoToken,
            $"Internal: unknown arithmetic coercion: {arithmeticCoercion.Coercion}")
        };
        WriteText(func);
        break;
      case BinaryOperator op:
        WriteText(BinaryOpToLean(op.Op));
        break;
      case FunctionCall fc:
        WriteText(Name(fc.Func));
        break;
      case IsConstructor isConstructor:
        throw new LeanConversionException(isConstructor.tok,
          $"Unsupported: Constructor: {isConstructor.ConstructorName}");
        // Discriminator functions not declared yet
        //Text($"is_{SanitizeNameForLean(isConstructor.ConstructorName)}");
        //break;
      case MapSelect:
        usesMaps = true;
        WriteText($"select{fun.ArgumentCount - 1}");
        break;
      case MapStore:
        usesMaps = true;
        WriteText($"store{fun.ArgumentCount - 2}");
        break;
      case UnaryOperator op:
        WriteText(UnaryOpToLean(op.Op));
        break;
      default:
        throw new LeanConversionException(Token.NoToken,
          $"Unsupported: IAppliable: {fun}");
    }
  }

  public override Expr VisitOldExpr(OldExpr node)
  {
    throw new LeanConversionException(node.tok, "Unsupported: OldExpr");
  }

  public override Type VisitFloatType(FloatType node)
  {
    throw new LeanConversionException(node.tok, "Unsupported: FloatType");
  }

  public override Requires VisitRequires(Requires requires)
  {
    return requires; // Already inlined
  }

  public override Ensures VisitEnsures(Ensures ensures)
  {
    return ensures; // Already inlined
  }

  public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
  {
    throw new LeanConversionException(node.tok, $"Unsupported: DeclWithFormals ({node}).");
  }

  public override Type VisitBvTypeProxy(BvTypeProxy node)
  {
    throw new LeanConversionException(node.tok, $"Unsupported: BvTypeProxy ({node}).");
  }

  public override Expr VisitCodeExpr(CodeExpr node)
  {
    throw new LeanConversionException(node.tok, $"Unsupported: CodeExpr ({node}).");
  }

  public override Cmd VisitCommentCmd(CommentCmd node)
  {
    // Comments are safe to ignore
    return node;
  }

  public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
  {
    return requiresSeq; // Already inlined
  }

  public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
  {
    return ensuresSeq; // Already inlined
  }

  public override Type VisitMapTypeProxy(MapTypeProxy node)
  {
    throw new LeanConversionException(node.tok, $"Unsupported: MapTypeProxy: {node}");
  }

  public override QKeyValue VisitQKeyValue(QKeyValue node)
  {
    // Implement this if we want to visit attributes? Or maybe extract them more directly.
    return node;
  }

  public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
  {
    // TODO: wrap in `mutual ... end` when necessary
    var name = Name(node);
    if (node is DatatypeTypeCtorDecl dt) {
      WriteLine($"inductive {name} where");
      foreach (var ctor in dt.Constructors) {
        Indent(1, $"| {Name(ctor)} : ");
        ctor.InParams.ForEach(p =>
        {
          Visit(p.TypedIdent.Type);
          WriteText(" → ");
        });
        WriteLine($" {name}");
      }
    } else {
      var tyStr = String.Join(" → ", Enumerable.Repeat("Type", node.Arity + 1).ToList());
      WriteLine($"axiom {name} : {tyStr}");

      if(node.Arity == 0) {
        WriteLine($"instance {name}BEq : BEq {name} := by sorry");
      }
    }
    return node;
  }

  public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
  {
    return VisitType(node.ExpandedType);
  }

  public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
  {
    var name = Name(node);
    WriteText($"def {name}");
    node.TypeParameters.ForEach(tp => WriteText($" ({Name(tp)} : Type)"));
    WriteText(" := ");
    Visit(node.Body);
    WriteLine();
    return node;
  }

  public override Type VisitTypeProxy(TypeProxy node)
  {
    var p = node.ProxyFor;
    if (p is null) {
      WriteText(Name(node));
    } else {
      VisitType(p);
    }
    return node;
  }

  public override Type VisitTypeVariable(TypeVariable node)
  {
    WriteText(Name(node));
    return node;
  }

  public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    WriteLine(" $");
    return node;
  }

  public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
  {
    Indent(2, "assert ");
    VisitExpr(node.Expr);
    WriteLine(" $");
    return node;
  }

  public override ActionDeclRef VisitActionDeclRef(ActionDeclRef node)
  {
    throw new LeanConversionException(node.tok, $"Unsupported: ActionDeclRef ({node}).");
  }

  public override Axiom VisitAxiom(Axiom node)
  {
    // This will take two more steps:
    // * A named lemma with a definition of `by sorry` (using a `name` attribute?) (or `id`, so it's also useful for coverage?)
    // * A named lemma that's defined by a call to a previously-defined proof of the same thing
    int n = 0;
    var name = $"ax_l{node.tok.line}c{node.tok.col}";
    while (userAxiomNames.Contains(name)) {
      name = $"ax_l{node.tok.line}c{node.tok.col}_{n}";
      n += 1;
    }
    WriteText($"axiom {name}: ");
    VisitExpr(node.Expr);
    WriteLine();
    userAxiomNames.Add(name);
    return node;
  }

  public override Function VisitFunction(Function node)
  {
    // In the long run, this should define functions when possible.
    WriteText($"axiom {Name(node)} : ");
    node.TypeParameters.ForEach(x =>
    {
      WriteText($"{{{Name(x)} : Type}}");
      WriteText($" {ArrowString} ");
    });
    node.InParams.ForEach(x =>
    {
      Visit(x.TypedIdent.Type);
      WriteText($" {ArrowString} ");
    });
    if (node.OutParams.Count == 1) {
      Visit(node.OutParams[0].TypedIdent.Type);
    } else {
      WriteText("(");
      node.OutParams.ForEach(x =>
      {
        Visit(x.TypedIdent.Type); WriteText(", ");
      });
      WriteText(")");
    }

    WriteLine();
    // Note: definition axioms will be emitted later
    // node.DefinitionAxioms.ForEach(ax => VisitAxiom(ax));
    return node;
  }

  private string BinaryOpToLean(BinaryOperator.Opcode op)
  {
    return op switch
    {
      BinaryOperator.Opcode.Add => "+",
      BinaryOperator.Opcode.Sub => "-",
      BinaryOperator.Opcode.Mul => "*",
      BinaryOperator.Opcode.Div => "/",
      BinaryOperator.Opcode.Mod => "%",
      BinaryOperator.Opcode.Lt => "<",
      BinaryOperator.Opcode.Gt => ">",
      BinaryOperator.Opcode.Le => "<=",
      BinaryOperator.Opcode.Ge => ">=",
      BinaryOperator.Opcode.Eq => "=",
      BinaryOperator.Opcode.Neq => NeqString,
      BinaryOperator.Opcode.And => AndString,
      BinaryOperator.Opcode.Or => OrString,
      BinaryOperator.Opcode.Iff => "=",
      BinaryOperator.Opcode.Imp => ArrowString,
      BinaryOperator.Opcode.Pow => "^",
      BinaryOperator.Opcode.RealDiv => "/",
      BinaryOperator.Opcode.FloatDiv => "/",
      _ => throw new LeanConversionException(Token.NoToken,
        $"Unsupported binary operator: {op.ToString()}")
    };
  }

  private string UnaryOpToLean(UnaryOperator.Opcode op)
  {
    return op switch
    {
      UnaryOperator.Opcode.Not => "Not",
      UnaryOperator.Opcode.Neg => "-",
      _ => throw new LeanConversionException(Token.NoToken,
        $"Unsupported unary operator: {op.ToString()}")
    };
  }

  private string SanitizeNameForLean(string name)
  {
    return "_boogie_" + name
      .Replace('@', '_')
      .Replace('.', '_')
      .Replace('#', '_')
      .Replace("$", "_dollar_");
  }

  private string Name(NamedDeclaration d)
  {
    return SanitizeNameForLean(d.Name);
  }

  private string Name(TypeVariable tv)
  {
    return SanitizeNameForLean(tv.Name);
  }

  private string Name(TypeProxy tp)
  {
    return SanitizeNameForLean(tp.Name);
  }

  private string BlockName(Block b)
  {
    return "β_" + SanitizeNameForLean(b.Label);
  }

  public override Procedure VisitProcedure(Procedure node)
  {
    return node;
  }

  private void WriteParams(Implementation node)
  {
    node.InParams.ForEach(x =>
    {
      Indent();
      VisitTypedIdent(x.TypedIdent);
      WriteLine();
    });
    node.OutParams.ForEach(x =>
    {
      Indent();
      VisitTypedIdent(x.TypedIdent);
      WriteLine();
    });
    node.LocVars.ForEach(x =>
    {
      Indent();
      VisitTypedIdent(x.TypedIdent);
      WriteLine();
    });
  }

  public override Implementation VisitImplementation(Implementation node)
  {
    var name = Name(node);
    var entryLabel = BlockName(node.Blocks[0]);

    usedNames.Clear(); // Skip any globals used only by axioms, etc.
    WriteLine();
    WriteLine($"namespace impl_{name}");
    WriteLine();

    WriteLine("@[simp]");
    WriteLine($"def {name}");
    WriteParams(node);
    IndentLine(1, $": Prop := {entryLabel}");
    IndentLine(1, "where");
    node.Blocks.ForEach(b => VisitBlock(b));
    WriteLine();
    WriteLine($"theorem {name}_correct");
    WriteParams(node);
    var paramNames =
      globalVars.Select(Name).Where(x => usedNames.Contains(x))
        .Concat(node.InParams.Select(Name))
        .Concat(node.OutParams.Select(Name))
        .Concat(node.LocVars.Select(Name));
    var paramString = String.Join(' ', paramNames);
    Indent(1, $": {name} {paramString} := by"); WriteLine();
    IndentLine(2, "try simp"); // Uses `try` because it may make no progress
    IndentLine(2, "try auto"); // Uses `try` because there may be no goals remaining
    var axiomNames = usesMaps ? mapAxiomNames.Concat(userAxiomNames) : userAxiomNames;
    Indent(3); WriteList(axiomNames); WriteLine();
    IndentLine(3, "u[]");
    WriteLine();
    WriteLine($"end impl_{name}");

    usesMaps = false; // Skip map axioms in the next implementation if it doesn't need them
    usedNames.Clear(); // Skip any globals not used by the next implementation

    return node;
  }

  /* ==== Nodes that should never be visited ==== */

  public override Program VisitProgram(Program node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Program should never be directly visited.");
  }

  public override Declaration VisitDeclaration(Declaration node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Declaration should never be directly visited.");
  }

  public override List<Declaration> VisitDeclarationList(List<Declaration> declarationList)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<Declaration> should never be directly visited ({declarationList}).");
  }

  public override List<Block> VisitBlockSeq(List<Block> blockSeq)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<Block> should never be directly visited ({blockSeq}).");
  }

  public override List<Block> VisitBlockList(List<Block> blocks)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<Block> should never be directly visited ({blocks}).");
  }

  public override Trigger VisitTrigger(Trigger node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Trigger should never be directly visited.");
  }

  public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<Expr> should never be directly visited ({exprSeq}).");
  }

  public override BoundVariable VisitBoundVariable(BoundVariable node)
  {
    throw new LeanConversionException(node.tok, $"Internal: BoundVariable should never be directly visited.");
  }

  public override Formal VisitFormal(Formal node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Formal should never be directly visited.");
  }

  public override LocalVariable VisitLocalVariable(LocalVariable node)
  {
    throw new LeanConversionException(node.tok, $"Internal error: LocalVariable should never be directly visited.");
  }

  public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node)
  {
    throw new LeanConversionException(node.tok, $"Internal: UnresolvedTypeIdentifier should never appear.");
  }

  public override Variable VisitVariable(Variable node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Variable should never be directly visited.");
  }

  public override List<Variable> VisitVariableSeq(List<Variable> variableSeq)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<Variable> should never be directly visited ({variableSeq}).");
  }

  public override HashSet<Variable> VisitVariableSet(HashSet<Variable> node)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: HashSet<Variable> should never be directly visited ({node}).");
  }

  public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
  {
    throw new LeanConversionException(node.tok, $"Internal: MapAssignLhs should never appear in passive program.");
  }

  public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
  {
    throw new LeanConversionException(node.tok, $"Internal: SimpleAssignLhs should never appear in passive program.");
  }

  public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
  {
    throw new LeanConversionException(node.tok, $"Internal: FieldAssignLhs should never appear in passive program.");
  }

  public override Cmd VisitAssignCmd(AssignCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: AssignCmd should never appear in passive program.");
  }

  public override Cmd VisitUnpackCmd(UnpackCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: UnpackCmd should never appear in passive program.");
  }

  public override Cmd VisitCallCmd(CallCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: CallCmd should never appear in passive program.");
  }

  public override Cmd VisitParCallCmd(ParCallCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: ParCallCmd should never appear in passive program.");
  }

  public override Cmd VisitHavocCmd(HavocCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: HavocCmd should never appear in passive program.");
  }

  public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: ReturnExprCmd should never appear in passive program.");
  }

  public override Cmd VisitStateCmd(StateCmd node)
  {
    throw new LeanConversionException(node.tok, $"Internal: StateCmd should never appear in passive program.");
  }

  public override List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<CallCmd> should never appear in passive program ({callCmds}).");
  }

  public override Procedure VisitActionDecl(ActionDecl node)
  {
    throw new LeanConversionException(node.tok, $"Internal: ActionDecl should never appear in passive program.");
  }

  public override YieldingLoop VisitYieldingLoop(YieldingLoop node)
  {
    throw new LeanConversionException(Token.NoToken,$"Internal: YieldingLoop should never appear in passive program ({node}).");
  }

  public override Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: YieldingLoops should never appear in passive program.");
  }

  public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node)
  {
    throw new LeanConversionException(node.tok, $"Internal: YieldProcedureDecl should never appear in passive program.");
  }

  public override Procedure VisitYieldInvariantDecl(YieldInvariantDecl node)
  {
    throw new LeanConversionException(node.tok, $"Internal: YieldInvariantDecl should never appear in passive program.");
  }

  public override Cmd VisitRE(RE node)
  {
    throw new LeanConversionException(node.tok, $"Internal: RE should never appear in passive program.");
  }

  public override List<RE> VisitRESeq(List<RE> reSeq)
  {
    throw new LeanConversionException(Token.NoToken, $"Internal: List<RE> should never appear in passive program ({reSeq})");
  }

  public override AtomicRE VisitAtomicRE(AtomicRE node)
  {
    throw new LeanConversionException(node.tok, $"Internal: AtomicRE should never appear in passive program.");
  }

  public override Choice VisitChoice(Choice node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Choice should never appear in passive program.");
  }

  public override Sequential VisitSequential(Sequential node)
  {
    throw new LeanConversionException(node.tok, $"Internal: Sequential should never appear in passive program.");
  }
}
