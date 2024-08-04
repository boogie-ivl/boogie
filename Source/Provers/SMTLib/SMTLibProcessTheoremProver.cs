using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text;

namespace Microsoft.Boogie.SMTLib
{
  public abstract class SMTLibProcessTheoremProver : ProverInterface
  {
    protected SMTLibSolver Process;
    protected SMTLibOptions libOptions;
    protected SMTLibProverContext ctx;
    protected VCExpressionGenerator gen;
    protected SMTLibSolverOptions options;
    protected IEnumerable<OptionValue> additionalSmtOptions = Array.Empty<OptionValue>();
    protected bool usingUnsatCore;
    private string backgroundPredicates;

    protected internal TypeAxiomBuilder AxBuilder { get; set; }
    protected TypeAxiomBuilder CachedAxBuilder;
    protected internal abstract ScopedNamer Namer { get; }
    protected TypeDeclCollector DeclCollector;

    protected bool HadErrors { get; set; }
    
    protected StringBuilder common = new();
    protected string CachedCommon = null;
    protected TextWriter currentLogFile;
    protected volatile ErrorHandler currentErrorHandler;
    
    [ContractInvariantMethod]
    private void ObjectInvariant()
    {
      Contract.Invariant(ctx != null);
      Contract.Invariant(Namer != null);
      Contract.Invariant(DeclCollector != null);
      Contract.Invariant(Cce.NonNullElements(Axioms));
      Contract.Invariant(Cce.NonNullElements(TypeDecls));
      Contract.Invariant(backgroundPredicates != null);
    }

    [NotDelayed]
    public SMTLibProcessTheoremProver(SMTLibOptions libOptions, SMTLibSolverOptions options, VCExpressionGenerator gen,
      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);

      this.options = options;
      this.libOptions = libOptions;
      this.ctx = ctx;
      this.gen = gen;
      usingUnsatCore = false;

      InitializeGlobalInformation();
      SetupAxiomBuilder(gen);

      ctx.parent = this;

      if (libOptions.ImmediatelyAcceptCommands)
      {
        // Prepare for ApiChecker usage
        if (options.LogFilename != null && currentLogFile == null)
        {
          currentLogFile = OpenOutputFile("");
        }
      }
    }
    protected static ScopedNamer GetNamer(SMTLibOptions libOptions, ProverOptions options, ScopedNamer namer = null)
    {
      return (options.RandomSeed, libOptions.NormalizeNames) switch
      {
        (0, true) => NormalizeNamer.Create(namer),
        (0, false) => KeepOriginalNamer.Create(namer),
        _ => RandomiseNamer.Create(new Random(options.RandomSeed), namer)
      };
    }

    protected ScopedNamer ResetNamer(ScopedNamer namer) {
      return GetNamer(libOptions, options, namer);
    }

    public override void AssertNamed(VCExpr vc, bool polarity, string name)
    {
      string vcString;
      if (polarity)
      {
        vcString = VCExpr2String(vc, 1);
      }
      else
      {
        vcString = "(not " + VCExpr2String(vc, 1) + ")";
      }

      AssertAxioms();
      SendThisVC(string.Format("(assert (! {0} :named {1}))", vcString, name));
    }

    protected void SetupAxiomBuilder(VCExpressionGenerator gen)
    {
      switch (libOptions.TypeEncodingMethod)
      {
        case CoreOptions.TypeEncoding.Arguments:
          AxBuilder = new TypeAxiomBuilderArguments(gen, libOptions);
          AxBuilder.Setup(options.UsedTypes);
          break;
        case CoreOptions.TypeEncoding.Monomorphic:
          AxBuilder = null;
          break;
        default:
          AxBuilder = new TypeAxiomBuilderPremisses(gen, libOptions);
          AxBuilder.Setup(options.UsedTypes);
          break;
      }
    }

    public override ProverContext Context
    {
      get
      {
        Contract.Ensures(Contract.Result<ProverContext>() != null);
        return ctx;
      }
    }

    private void FeedTypeDeclsToProver()
    {
      foreach (string s in DeclCollector.GetNewDeclarations())
      {
        Contract.Assert(s != null);
        AddTypeDecl(s);
      }
    }

    protected static string Sanitize(string msg)
    {
      var idx = msg.IndexOf('\n');
      if (idx > 0)
      {
        msg = msg.Replace("\r", "").Replace("\n", "\r\n");
      }

      return msg;
    }

    public override void LogComment(string comment)
    {
      SendCommon("; " + comment);
    }

    private void SendCommon(string s)
    {
      Send(s, true);
    }

    protected void SendThisVC(string s)
    {
      Send(s, false);
    }

    protected abstract void Send(string s, bool isCommon);

    private void FindDependentTypes(Type type, List<DatatypeTypeCtorDecl> dependentTypes)
    {
      DeclCollector.TypeToStringReg(type);
      if (type.IsSeq)
      {
        FindDependentTypes(type.AsCtor.Arguments[0], dependentTypes);
      }
      MapType mapType = type as MapType;
      if (mapType != null)
      {
        foreach (Type t in mapType.Arguments)
        {
          FindDependentTypes(t, dependentTypes);
        }
        FindDependentTypes(mapType.Result, dependentTypes);
      }
      if (type is CtorType ctorType && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl &&
          ctx.KnownDatatypes.Contains(datatypeTypeCtorDecl))
      {
        dependentTypes.Add(datatypeTypeCtorDecl);
      }
    }

    private void PrepareDataTypes()
    {
      if (ctx.KnownDatatypes.Count > 0)
      {
        GraphUtil.Graph<DatatypeTypeCtorDecl> dependencyGraph = new GraphUtil.Graph<DatatypeTypeCtorDecl>();
        foreach (var datatype in ctx.KnownDatatypes)
        {
          dependencyGraph.AddSource(datatype);
          foreach (Function f in datatype.Constructors)
          {
            var dependentTypes = new List<DatatypeTypeCtorDecl>();
            foreach (Variable v in f.InParams)
            {
              FindDependentTypes(v.TypedIdent.Type, dependentTypes);
            }
            foreach (var result in dependentTypes)
            {
              dependencyGraph.AddEdge(datatype, result);
            }
          }
        }

        GraphUtil.StronglyConnectedComponents<DatatypeTypeCtorDecl> sccs =
          new GraphUtil.StronglyConnectedComponents<DatatypeTypeCtorDecl>(dependencyGraph.Nodes, dependencyGraph.Predecessors,
            dependencyGraph.Successors);
        sccs.Compute();
        foreach (GraphUtil.SCC<DatatypeTypeCtorDecl> scc in sccs)
        {
          string datatypesString = "";
          string datatypeConstructorsString = "";
          foreach (var datatype in scc)
          {
            datatypesString += "(" + new SMTLibExprLineariser(libOptions).TypeToString(new CtorType(Token.NoToken, datatype, new List<Type>())) + " 0)";
            string datatypeConstructorString = "";
            foreach (Function f in datatype.Constructors)
            {
              string quotedConstructorName = Namer.GetQuotedName(f, f.Name);
              datatypeConstructorString += "(" + quotedConstructorName + " ";
              foreach (Variable v in f.InParams)
              {
                string quotedSelectorName = Namer.GetQuotedName(v, v.Name + "#" + f.Name);
                datatypeConstructorString += "(" + quotedSelectorName + " " +
                                             DeclCollector.TypeToStringReg(v.TypedIdent.Type) + ") ";
              }

              datatypeConstructorString += ") ";
            }

            datatypeConstructorsString += "(" + datatypeConstructorString + ") ";
          }

          List<string> decls = DeclCollector.GetNewDeclarations();
          foreach (string decl in decls)
          {
            SendCommon(decl);
          }

          SendCommon("(declare-datatypes (" + datatypesString + ") (" + datatypeConstructorsString + "))");
        }
      }
    }

    private void PrepareFunctionDefinitions()
    {
      // Collect all function definitions to be processed
      Stack<Function> functionDefs = new Stack<Function>();
      foreach (Function f in ctx.DefinedFunctions.Keys)
      {
        DeclCollector.AddKnownFunction(f); // add func to knows funcs so that it does not get declared later on
        functionDefs.Push(f);
      }

      // Process each definition, but also be sure to process dependencies first in case one
      // definition calls another.
      // Also check for definition cycles.
      List<string> generatedFuncDefs = new List<string>();
      FunctionDependencyCollector collector = new FunctionDependencyCollector();
      HashSet<Function> definitionAdded = new HashSet<Function>(); // whether definition has been fully processed
      HashSet<Function>
        dependenciesComputed = new HashSet<Function>(); // whether dependencies have already been computed
      while (functionDefs.Count > 0)
      {
        Function f = functionDefs.Peek();
        if (definitionAdded.Contains(f))
        {
          // This definition was already processed (as a dependency of another definition)
          functionDefs.Pop();
          continue;
        }

        // Grab the definition and then compute the dependencies.
        Contract.Assert(ctx.DefinedFunctions.ContainsKey(f));
        VCExprNAry defBody = ctx.DefinedFunctions[f];
        List<Function> dependencies = collector.Collect(defBody[1]);
        bool hasDependencies = false;
        foreach (Function fdep in dependencies)
        {
          if (ctx.DefinedFunctions.ContainsKey(fdep) && !definitionAdded.Contains(fdep))
          {
            // Handle dependencies first
            functionDefs.Push(fdep);
            hasDependencies = true;
          }
        }

        if (!hasDependencies)
        {
          // No dependencies: go ahead and process this definition.
          string funcDef = "(define-fun ";
          var funCall = defBody[0] as VCExprNAry;
          Contract.Assert(funCall != null);
          VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp) funCall.Op;
          Contract.Assert(op != null);
          funcDef += Namer.GetQuotedName(op.Func, op.Func.Name);

          funcDef += " (";
          foreach (var v in funCall.UniformArguments)
          {
            VCExprVar varExpr = v as VCExprVar;
            Contract.Assert(varExpr != null);
            DeclCollector.AddKnownVariable(varExpr); // add var to knows vars so that it does not get declared later on
            string printedName = Namer.GetQuotedLocalName(varExpr, varExpr.Name);
            Contract.Assert(printedName != null);
            funcDef += "(" + printedName + " " + new SMTLibExprLineariser(libOptions).TypeToString(varExpr.Type) + ") ";
          }

          funcDef += ") ";

          funcDef += new SMTLibExprLineariser(libOptions).TypeToString(defBody[0].Type) + " ";
          funcDef += VCExpr2String(defBody[1], -1);
          funcDef += ")";
          generatedFuncDefs.Add(funcDef);
          definitionAdded.Add(f);
          functionDefs.Pop();
        }
        else
        {
          dependenciesComputed.Add(f);
        }
      }

      FlushAxioms(); // Flush all dependencies before flushing function definitions
      generatedFuncDefs.ForEach(SendCommon); // Flush function definitions
    }

    protected virtual void PrepareCommon()
    {
      if (common.Length == 0)
      {
        SendCommon("(set-option :print-success false)");
        SendCommon("(set-info :smt-lib-version 2.6)");
        if (libOptions.ProduceModel)
        {
          SendCommon("(set-option :produce-models true)");
        }

        foreach (var opt in SmtOptions())
        {
          SendCommon("(set-option :" + opt.Option + " " + opt.Value + ")");
        }

        if (!string.IsNullOrEmpty(options.Logic))
        {
          SendCommon("(set-logic " + options.Logic + ")");
        }

        // Set produce-unsat-cores last. It seems there's a bug in Z3 where if we set it earlier its value
        // gets reset by other set-option commands ( https://z3.codeplex.com/workitem/188 )
        if (libOptions.ProduceUnsatCores)
        {
          SendCommon("(set-option :produce-unsat-cores true)");
          this.usingUnsatCore = true;
        }

        SendCommon("; done setting options\n");
        SendCommon(backgroundPredicates);

        if (options.UseTickleBool)
        {
          SendCommon("(declare-fun tickleBool (Bool) Bool)");
          SendCommon("(assert (and (tickleBool true) (tickleBool false)))");
        }

        if (libOptions.RunDiagnosticsOnTimeout)
        {
          SendCommon("(declare-fun timeoutDiagnostics (Int) Bool)");
        }

        PrepareDataTypes();

        if (libOptions.ProverPreamble != null)
        {
          SendCommon("(include \"" + libOptions.ProverPreamble + "\")");
        }

        PrepareFunctionDefinitions();
      }

      if (!AxiomsAreSetup) {
        SetupAxioms();
      }
    }

    private IEnumerable<OptionValue> SmtOptions()
    {
      return options.SmtOptions.Concat(additionalSmtOptions);
    }

    private void SetupAxioms()
    {
      var axioms = ctx.Axioms;
      if (axioms is VCExprNAry nary && nary.Op == VCExpressionGenerator.AndOp) {
        foreach (var expr in nary.UniformArguments) {
          var str = VCExpr2String(expr, -1);
          if (str != "true") {
            AddAxiom(str);
          }
        }
      } else {
        AddAxiom(VCExpr2String(axioms, -1));
      }

      AxiomsAreSetup = true;
      CachedAxBuilder = AxBuilder;
    }

    protected void FlushAxioms()
    {
      TypeDecls.ForEach(SendCommon);
      TypeDecls.Clear();
      foreach (string s in Axioms)
      {
        Contract.Assert(s != null);
        if (s != "true")
        {
          SendCommon("(assert " + s + ")");
        }
      }

      Axioms.Clear();
      //FlushPushedAssertions();
    }

    protected void SendVCOptions()
    {
      if (options.Solver == SolverKind.Z3 || options.Solver == SolverKind.NoOpWithZ3Options)
      {
        SendThisVC("(set-option :" + Z3.TimeoutOption + " " + options.TimeLimit + ")");
        SendThisVC("(set-option :" + Z3.RlimitOption + " " + options.ResourceLimit + ")");
        if (options.RandomSeed != 0) {
          SendThisVC("(set-option :" + Z3.SmtRandomSeed + " " + options.RandomSeed + ")");
          SendThisVC("(set-option :" + Z3.SatRandomSeed + " " + options.RandomSeed + ")");
        }
      }

      foreach (var opt in SmtOptions())
      {
        SendThisVC("(set-option :" + opt.Option + " " + opt.Value + ")");
      }
    }

    protected void SendVCId(string descriptiveName)
    {
      if (this.libOptions.EmitDebugInformation) {
        SendThisVC("(set-info :boogie-vc-id " + SmtLibNameUtils.QuoteId(descriptiveName) + ")");
      }
    }

    protected void CloseLogFile()
    {
      if (currentLogFile != null)
      {
        currentLogFile.Close();
        currentLogFile = null;
      }
    }

    protected void FlushLogFile()
    {
      if (currentLogFile != null)
      {
        currentLogFile.Flush();
      }
    }

    protected void SendOptimizationRequests()
    {
      if (options.Solver == SolverKind.Z3 && 0 < OptimizationRequests.Count)
      {
        foreach (var r in OptimizationRequests)
        {
          SendThisVC(r);
        }
      }
    }

    private class BadExprFromProver : Exception
    {
    }

    private class MyFileParser : SExpr.Parser
    {
      private SMTLibProcessTheoremProver parent;

      public MyFileParser(System.IO.StreamReader _sr, SMTLibProcessTheoremProver _parent)
        : base(_sr)
      {
        parent = _parent;
      }

      public override void ParseError(string msg)
      {
        parent.HandleProverError("Error in conjecture file from prover: " + msg);
      }
    }

    private static HashSet<string> usedLogNames = new HashSet<string>();

    protected TextWriter OpenOutputFile(string descriptiveName)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Ensures(Contract.Result<TextWriter>() != null);

      string filenameTemplate = options.LogFilename;
      var (filename, reused) = Helpers.GetLogFilename(descriptiveName, filenameTemplate, false);

      return new StreamWriter(filename, reused);
    }

    protected void HandleProverError(string s)
    {
      // Trying to match prover warnings of the form:
      // - for Z3: WARNING: warning_message
      // - for CVC5: query.smt2:222.24: warning: warning_message
      // All other lines are considered to be errors.

      s = s.Replace("\r", "");
      const string ProverWarning = "WARNING: ";
      string errors = "";
      
      foreach (var line in s.Split('\n'))
      {
        int idx = line.IndexOf(ProverWarning, StringComparison.OrdinalIgnoreCase);
        if (idx >= 0)
        {
          string warn = line.Substring(idx + ProverWarning.Length);
          currentErrorHandler?.OnProverWarning(warn);
        }
        else
        {
          errors += (line + "\n");
        }
      }

      if (errors == "")
      {
        return;
      }
      
      libOptions.OutputWriter.WriteLine("Prover error: " + errors);

      var handler = currentErrorHandler;
      handler?.OnProverError(errors);
      HadErrors = true;
    }

    protected class SMTErrorModelConverter
    {
      private List<SExpr> ErrorModelTodo;
      private SMTLibProcessTheoremProver Parent;
      private StringBuilder ErrorModel = new StringBuilder();
      private HashSet<SExpr> TopLevelProcessed = new HashSet<SExpr>();
      private int NumNewArrays = 0;
      private Dictionary<string, int> SortSet = new Dictionary<string, int>();

      private Dictionary<string, Dictionary<string, List<SExpr>>> DataTypes =
        new Dictionary<string, Dictionary<string, List<SExpr>>>();

      private Dictionary<string, SExpr> Functions = new Dictionary<string, SExpr>();

      public SMTErrorModelConverter(SExpr _ErrorModel, SMTLibProcessTheoremProver _Parent)
      {
        ErrorModelTodo = _ErrorModel.Arguments.ToList();
        Parent = _Parent;
      }

      public string Convert()
      {
        ConvertErrorModel(ErrorModel);
        return ErrorModel.ToString();
      }

      private bool IsConstArray(SExpr element, SExpr type)
      {
        if (type.Name != "Array")
        {
          return false;
        }

        if (element.Name == "__array_store_all__")
        {
          return true;
        }
        else if (element.Name == "" && element[0].Name == "as" &&
                 element[0][0].Name == "const")
        {
          return true;
        }

        return false;
      }

      private SExpr GetConstArrayElement(SExpr element)
      {
        if (element.Name == "__array_store_all__")
        {
          return element[1];
        }
        else if (element.Name == "" && element[0].Name == "as" &&
                 element[0][0].Name == "const")
        {
          return element[1];
        }

        Parent.HandleProverError("Unexpected value: " + element);
        throw new BadExprFromProver();
      }

      private void ConstructComplexValue(SExpr element, SExpr type, StringBuilder m)
      {
        if (type.Name == "Array")
        {
          if (element.Name == "store" || IsConstArray(element, type))
          {
            NumNewArrays++;
            m.Append("as-array[k!" + NumNewArrays + ']');
            SExpr[] args = {new SExpr("k!" + NumNewArrays), new SExpr(""), type, element};
            var newElement = new SExpr("define-fun", args);
            TopLevelProcessed.Add(newElement);
            ErrorModelTodo.Add(newElement);
            return;
          }
        }

        ConstructSimpleValue(element, type, m);
      }

      private void ConstructSimpleValue(SExpr element, SExpr type, StringBuilder m)
      {
        if (type.Name == "Bool" && element.ArgCount == 0)
        {
          m.Append(element.ToString());
          return;
        }

        if (type.Name == "Int")
        {
          if (element.ArgCount == 0)
          {
            m.Append(element.ToString());
            return;
          }
          else if (element.Name == "-" && element.ArgCount == 1)
          {
            m.Append(element.ToString());
            return;
          }
        }

        if (type.Name == "_" && type.ArgCount == 2 && type[0].Name == "BitVec")
        {
          if (element.Name == "_" && element.ArgCount == 2 &&
              element[0].Name.StartsWith("bv") && element[0].ArgCount == 0 &&
              element[1].Name == type.Arguments[1].Name && element[1].ArgCount == 0)
          {
            m.Append(element[0].Name + '[' + element[1].Name + ']');
            return;
          }
        }

        if (type.Name == "Array")
        {
          while (element.Name == "store")
          {
            ConstructComplexValue(element[1], type[0], m);
            m.Append(" -> ");
            ConstructComplexValue(element[2], type[1], m);
            m.Append("\n  ");
            if (element[0].Name != "store")
            {
              m.Append("else -> ");
            }

            element = element[0];
          }

          if (IsConstArray(element, type))
          {
            ConstructComplexValue(GetConstArrayElement(element), type[1], m);
            return;
          }
          else if (element.Name == "_" && element.ArgCount == 2 &&
                   element[0].Name == "as-array")
          {
            m.Append("as-array[" + element[1].Name + ']');
            return;
          }
        }

        if (type.Name == "Seq")
        {
          if (element.Name == "as")
          {
            m.Append(element[0]);
            return;
          }
        }
        
        if (SortSet.ContainsKey(type.Name) && SortSet[type.Name] == 0)
        {
          var prefix = "@uc_T@" + type.Name.Substring(2) + "_";
          var elementName =  element.Name;
          if (elementName == "as")
          {
            elementName = element[0].Name;
          }
          if (elementName.StartsWith(prefix))
          {
            m.Append(type.Name + "!val!" + elementName.Substring(prefix.Length));
            return;
          }
        }

        if (Functions.ContainsKey(element.Name) &&
            type.Name == Functions[element.Name].Name)
        {
          m.Append(element.Name);
          return;
        }

        if (DataTypes.ContainsKey(type.Name) &&
            DataTypes[type.Name].ContainsKey(element.Name) &&
            element.ArgCount == DataTypes[type.Name][element.Name].Count)
        {
          m.Append("(" + element.Name);
          for (int i = 0; i < element.ArgCount; ++i)
          {
            m.Append(" ");
            ConstructComplexValue(element[i], DataTypes[type.Name][element.Name][i], m);
          }

          m.Append(")");
          return;
        }

        Parent.HandleProverError("Unexpected value: " + element);
        throw new BadExprFromProver();
      }

      private void ConstructFunctionArguments(SExpr arguments, List<SExpr> argTypes, StringBuilder[] argValues)
      {
        if (arguments.Name == "and")
        {
          ConstructFunctionArguments(arguments[0], argTypes, argValues);
          ConstructFunctionArguments(arguments[1], argTypes, argValues);
        }
        else if (arguments.Name == "=" &&
                 (arguments[0].Name.StartsWith("_ufmt_") || arguments[0].Name.StartsWith("x!") ||
                  arguments[0].Name.StartsWith("_arg_")))
        {
          int argNum;
          if (arguments[0].Name.StartsWith("_ufmt_"))
          {
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("_uftm_".Length)) - 1;
          }
          else if (arguments[0].Name.StartsWith("_arg_"))
          {
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("_arg_".Length)) - 1;
          }
          else /* if (arguments[0].Name.StartsWith("x!")) */
          {
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("x!".Length)) - 1;
          }

          if (argNum < 0 || argNum >= argTypes.Count)
          {
            Parent.HandleProverError("Unexpected function argument: " + arguments[0]);
            throw new BadExprFromProver();
          }

          if (argValues[argNum] != null)
          {
            Parent.HandleProverError("Function argument defined multiple times: " + arguments[0]);
            throw new BadExprFromProver();
          }

          argValues[argNum] = new StringBuilder();
          ConstructComplexValue(arguments[1], argTypes[argNum], argValues[argNum]);
        }
        else
        {
          Parent.HandleProverError("Unexpected function argument: " + arguments);
          throw new BadExprFromProver();
        }
      }

      private void ConstructFunctionElements(SExpr element, List<SExpr> argTypes, SExpr outType, StringBuilder m)
      {
        while (element.Name == "ite")
        {
          StringBuilder[] argValues = new StringBuilder[argTypes.Count];
          ConstructFunctionArguments(element[0], argTypes, argValues);
          foreach (var s in argValues)
          {
            m.Append(s + " ");
          }

          m.Append("-> ");
          ConstructComplexValue(element[1], outType, m);
          m.Append("\n  ");
          if (element[2].Name != "ite")
          {
            m.Append("else -> ");
          }

          element = element[2];
        }

        ConstructComplexValue(element, outType, m);
      }

      private void ConstructFunction(SExpr element, SExpr inType, SExpr outType, StringBuilder m)
      {
        List<SExpr> argTypes = new List<SExpr>();

        for (int i = 0; i < inType.ArgCount; ++i)
        {
          if (inType[i].Name != "_ufmt_" + (i + 1) && inType[i].Name != "x!" + (i + 1) &&
              !inType[i].Name.StartsWith("BOUND_VARIABLE_") && inType[i].Name != "_arg_" + (i + 1))
          {
            Parent.HandleProverError("Unexpected function argument: " + inType[i].Name);
            throw new BadExprFromProver();
          }

          argTypes.Add(inType[i][0]);
        }

        ConstructFunctionElements(element, argTypes, outType, m);
      }

      private void ConstructDefine(SExpr element, StringBuilder m)
      {
        Debug.Assert(element.Name == "define-fun");

        if (element[1].ArgCount != 0)
        {
          TopLevelProcessed.Add(element);
        }

        m.Append(element[0] + " -> ");
        if (TopLevelProcessed.Contains(element))
        {
          m.Append("{\n  ");
        }

        if (element[1].ArgCount == 0 && element[2].Name == "Array" && !TopLevelProcessed.Contains(element))
        {
          ConstructComplexValue(element[3], element[2], m);
        }
        else if (element[1].ArgCount == 0)
        {
          ConstructSimpleValue(element[3], element[2], m);
        }
        else
        {
          ConstructFunction(element[3], element[1], element[2], m);
        }

        if (TopLevelProcessed.Contains(element))
        {
          m.Append("\n}");
        }

        m.Append("\n");
      }

      private void ExtractDataType(SExpr datatypes)
      {
        Debug.Assert(datatypes.Name == "declare-datatypes");

        if (datatypes[0].Name != "" || datatypes[1].Name != "" || datatypes[0].ArgCount != datatypes[1].ArgCount)
        {
          Parent.HandleProverError("Unexpected datatype: " + datatypes);
          throw new BadExprFromProver();
        }

        for (int typeIndex = 0; typeIndex < datatypes[1].ArgCount; typeIndex++)
        {
          SExpr typeDef = datatypes[1][typeIndex];
          Dictionary<string, List<SExpr>> dataTypeConstructors = new Dictionary<string, List<SExpr>>();
          for (int j = 0; j < typeDef.ArgCount; ++j)
          {
            var argumentTypes = new List<SExpr>();
            for (int i = 0; i < typeDef[j].ArgCount; ++i)
            {
              if (typeDef[j][i].ArgCount != 1)
              {
                Parent.HandleProverError("Unexpected datatype constructor: " + typeDef[j]);
                throw new BadExprFromProver();
              }
              argumentTypes.Add(typeDef[j][i][0]);
            }
            dataTypeConstructors[typeDef[j].Name] = argumentTypes;
          }
          DataTypes[datatypes[0][typeIndex].Name] = dataTypeConstructors;
        }
      }

      private void ConvertErrorModel(StringBuilder m)
      {
        if (Parent.options.Solver == SolverKind.Z3 || Parent.options.Solver == SolverKind.CVC5)
        {
          // Datatype declarations are not returned by Z3 or CVC5, so parse common
          // instead. This is not very efficient, but currently not an issue for interfacing
          // with Z3 as this not the normal way of interfacing with Z3.
          var ms = new MemoryStream(Encoding.ASCII.GetBytes(Parent.common.ToString()));
          var sr = new StreamReader(ms);
          SExpr.Parser p = new MyFileParser(sr, null);
          var sexprs = p.ParseSExprs(false);
          foreach (var e in sexprs)
          {
            switch (e.Name)
            {
              case "declare-sort":
                SortSet[e[0].Name] = System.Convert.ToInt32(e[1].Name);
                break;
              case "declare-datatypes":
                ExtractDataType(e);
                break;
            }
          }
        }

        while (ErrorModelTodo.Count > 0)
        {
          var e = ErrorModelTodo[0];
          ErrorModelTodo.RemoveAt(0);

          switch (e.Name)
          {
            case "define-fun":
              ConstructDefine(e, m);
              break;
            case "declare-sort":
              SortSet[e[0].Name] = System.Convert.ToInt32(e[1].Name);
              break;
            case "declare-datatypes":
              ExtractDataType(e);
              break;
            case "declare-fun":
              if (e[1].Name != "" || e[1].ArgCount > 0 || e[2].ArgCount > 0 ||
                  e[2].Name == "Bool" || e[2].Name == "Int")
              {
                Parent.HandleProverError("Unexpected top level model element: " + e.Name);
                throw new BadExprFromProver();
              }
              Functions[e[0].Name] = e[2];
              break;
            case "forall":
              // ignore
              break;
            default:
              Parent.HandleProverError("Unexpected top level model element: " + e.Name);
              throw new BadExprFromProver();
          }
        }
      }
    }

    protected readonly IList<string> OptimizationRequests = new List<string>();

    protected string VCExpr2String(VCExpr expr, int polarity)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<string>() != null);

      lock (gen)
      {
        DateTime start = DateTime.UtcNow;

        // handle the types in the VCExpr
        VCExpr exprWithoutTypes;
        switch (libOptions.TypeEncodingMethod)
        {
          case CoreOptions.TypeEncoding.Arguments:
          {
            TypeEraser eraser = new TypeEraserArguments((TypeAxiomBuilderArguments) AxBuilder, gen);
            exprWithoutTypes = AxBuilder.Cast(eraser.Erase(expr, polarity), Type.Bool);
            break;
          }
          case CoreOptions.TypeEncoding.Monomorphic:
          {
            exprWithoutTypes = expr;
            break;
          }
          default:
          {
            TypeEraser eraser = new TypeEraserPremisses((TypeAxiomBuilderPremisses) AxBuilder, gen);
            exprWithoutTypes =  AxBuilder.Cast(eraser.Erase(expr, polarity), Type.Bool);
            break;
          }
        }
        Contract.Assert(exprWithoutTypes != null);

        LetBindingSorter letSorter = new LetBindingSorter(gen);
        Contract.Assert(letSorter != null);

        VCExpr sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
        Contract.Assert(sortedExpr != null);
        DeclCollector.Collect(sortedExpr);
        FeedTypeDeclsToProver();

        if (AxBuilder != null)
        {
          VCExpr sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);
          Contract.Assert(sortedAxioms != null);
          DeclCollector.Collect(sortedAxioms);
          FeedTypeDeclsToProver();
          AddAxiom(SMTLibExprLineariser.ToString(sortedAxioms, Namer, libOptions, options, namedAssumes: NamedAssumes));
        }

        string res = SMTLibExprLineariser.ToString(sortedExpr, Namer, libOptions, options, NamedAssumes, OptimizationRequests);
        Contract.Assert(res != null);

        if (libOptions.Trace)
        {
          DateTime end = DateTime.UtcNow;
          TimeSpan elapsed = end - start;
          if (elapsed.TotalSeconds > 0.5)
          {
            libOptions.OutputWriter.WriteLine("Linearising   [{0} s]", elapsed.TotalSeconds);
          }
        }

        return res;
      }
    }

    // the list of all known axioms, where have to be included in each
    // verification condition
    protected readonly List<string /*!>!*/> Axioms = new List<string /*!*/>();
    protected bool AxiomsAreSetup = false;

    // similarly, a list of function/predicate declarations
    protected readonly List<string /*!>!*/> TypeDecls = new List<string /*!*/>();

    protected void AddAxiom(string axiom)
    {
      Contract.Requires(axiom != null);
      Axioms.Add(axiom);
      //      if (thmProver != null) {
      //        LogActivity(":assume " + axiom);
      //        thmProver.AddAxioms(axiom);
      //      }
    }

    protected void AddTypeDecl(string decl)
    {
      Contract.Requires(decl != null);
      TypeDecls.Add(decl);
      //     if (thmProver != null) {
      //       LogActivity(decl);
      //       thmProver.Feed(decl, 0);
      //     }
    }

    ////////////////////////////////////////////////////////////////////////////

    private void InitializeGlobalInformation()
    {
      Contract.Ensures(backgroundPredicates != null);
      //throws ProverException, System.IO.FileNotFoundException;
      if (backgroundPredicates == null)
      {
        if (libOptions.TypeEncodingMethod == CoreOptions.TypeEncoding.Monomorphic)
        {
          backgroundPredicates = "";
        }
        else
        {
          backgroundPredicates = @"
(set-info :category ""industrial"")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)";
        }
      }
    }

    public override VCExpressionGenerator VCExprGen
    {
      get { return this.gen; }
    }

    //// Push/pop interface

    //List<string> pushedAssertions = new List<string>();
    //int numRealPushes;
    public override string VCExpressionToString(VCExpr vc)
    {
      return VCExpr2String(vc, 1);
    }

    public override void PushVCExpression(VCExpr vc)
    {
      throw new NotImplementedException();
    }

    public override void Pop()
    {
      SendThisVC("(pop 1)");
      DeclCollector.Pop();
    }

    public override int NumAxiomsPushed()
    {
      throw new NotImplementedException();
      //return numRealPushes + pushedAssertions.Count;
    }

    private void FlushPushedAssertions()
    {
      throw new NotImplementedException();
    }

    public override void Assert(VCExpr vc, bool polarity, bool isSoft = false, int weight = 1, string name = null)
    {
      OptimizationRequests.Clear();
      string assert = "assert";
      if (options.Solver == SolverKind.Z3 && isSoft)
      {
        assert += "-soft";
      }

      var expr = polarity ? VCExpr2String(vc, 1) : "(not\n" + VCExpr2String(vc, 1) + "\n)";
      if (options.Solver == SolverKind.Z3 && isSoft)
      {
        expr += " :weight " + weight;
      }

      if (name != null)
      {
        expr = "(! " + expr + ":named " + name + ")";
      }

      AssertAxioms();
      SendThisVC("(" + assert + " " + expr + ")");
      SendOptimizationRequests();
    }

    public override void DefineMacro(Macro f, VCExpr vc)
    {
      DeclCollector.AddKnownFunction(f);
      string printedName = Namer.GetQuotedName(f, f.Name);
      var argTypes = string.Join(" ", f.InParams.Select(p => DeclCollector.TypeToStringReg(p.TypedIdent.Type)));
      string decl = "(define-fun " + printedName + " (" + argTypes + ") " +
                    DeclCollector.TypeToStringReg(f.OutParams[0].TypedIdent.Type) + " " + VCExpr2String(vc, 1) + ")";
      AssertAxioms();
      SendThisVC(decl);
    }

    public override void AssertAxioms()
    {
      FlushAxioms();
    }

    public override void SetTimeout(uint ms)
    {
      options.TimeLimit = ms;
    }

    public override void SetRlimit(uint limit)
    {
      options.ResourceLimit = limit;
    }

    public override void SetAdditionalSmtOptions(IEnumerable<OptionValue> entries)
    {
      additionalSmtOptions = entries;
    }
    protected SolverOutcome ParseOutcome(SExpr resp, out bool wasUnknown)
    {
      var result = SolverOutcome.Undetermined;
      wasUnknown = false;

      if (resp is null) {
        wasUnknown = true;
        return result;
      }

      switch (resp.Name)
      {
        case "unsat":
          result = SolverOutcome.Valid;
          break;
        case "sat":
          result = SolverOutcome.Invalid;
          break;
        case "unknown":
          result = SolverOutcome.Invalid;
          wasUnknown = true;
          break;
        case "objectives":
          // We ignore this.
          break;
        case "error":
          if (resp.Arguments.Length == 1 && resp.Arguments[0].IsId &&
              (resp.Arguments[0].Name.Contains("max. resource limit exceeded")
               || resp.Arguments[0].Name.Contains("push canceled")
               || resp.Arguments[0].Name.Contains("resource limits reached")))
          {
            currentErrorHandler.OnResourceExceeded("max resource limit");
            result = SolverOutcome.OutOfResource;
          }
          else
          {
            HandleProverError("Unexpected prover response: " + resp);
          }
          break;
        default:
          HandleProverError("Unexpected prover response: " + resp);
          break;
      }

      return result;
    }

    protected SolverOutcome ParseReasonUnknown(SExpr resp, SolverOutcome initialOutcome)
    {
      SolverOutcome result;
      if (resp is null || resp.Name == "") {
        result = initialOutcome;
      }
      else if (resp.ArgCount == 1 && resp.Name == ":reason-unknown")
      {
        switch (resp[0].Name)
        {
          case "":
            result = initialOutcome;
            break;
          case "incomplete":
          case "(incomplete quantifiers)":
          case "(incomplete (theory arithmetic))":
          case "smt tactic failed to show goal to be sat/unsat (incomplete (theory arithmetic))":
            result = SolverOutcome.Invalid;
            break;
          case "memout":
            currentErrorHandler.OnResourceExceeded("memory");
            result = SolverOutcome.OutOfMemory;
            break;
          case "timeout":
            currentErrorHandler.OnResourceExceeded("timeout");
            result = SolverOutcome.TimeOut;
            break;
          case "canceled":
            // both timeout and max resource limit are reported as
            // canceled in version 4.4.1
            if (this.options.TimeLimit > 0)
            {
              currentErrorHandler.OnResourceExceeded("timeout");
              result = SolverOutcome.TimeOut;
            }
            else
            {
              currentErrorHandler.OnResourceExceeded("max resource limit");
              result = SolverOutcome.OutOfResource;
            }

            break;
          case "max. resource limit exceeded":
          case "resource limits reached":
          case "(resource limits reached)":
            currentErrorHandler.OnResourceExceeded("max resource limit");
            result = SolverOutcome.OutOfResource;
            break;
          case "unknown":
            result = SolverOutcome.Undetermined;
            break;
          default:
            result = SolverOutcome.Undetermined;
            HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp);
            break;
        }
      }
      else
      {
        result = SolverOutcome.Undetermined;
        HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp);
      }

      return result;
    }

    protected Model ParseErrorModel(SExpr resp)
    {
      if (resp is null || resp.Name == "error") {
        return null;
      }

      Model theModel = null;
      string modelStr = null;

      if (resp.ArgCount >= 1) {
        var converter = new SMTErrorModelConverter(resp, this);
        modelStr = converter.Convert();
      } else if (resp.ArgCount == 0 && resp.Name.Contains("->")) {
        modelStr = resp.Name;
      } else {
        HandleProverError("Unexpected prover response getting model: " + resp);
      }

      List<Model> models = null;
      try {
        switch (options.Solver) {
          case SolverKind.Z3:
          case SolverKind.CVC5:
            models = Model.ParseModels(new StringReader("Error model: \n" + modelStr), Namer.GetOriginalName);
            break;
          default:
            Debug.Assert(false);
            return null;
        }
      } catch (ArgumentException exn) {
        HandleProverError("Model parsing error: " + exn.Message);
      }

      if (models == null) {
        HandleProverError("Could not parse any models");
      } else if (models.Count == 0) {
        HandleProverError("Could not parse any models");
      } else if (models.Count > 1) {
        HandleProverError("Expecting only one model but got many");
      } else {
        theModel = models[0];
      }

      return theModel;
    }

    private static object ParseValueFromProver(SExpr expr)
    {
      return expr.ToString().Replace(" ", "").Replace("(", "").Replace(")", "");
    }

    private static SExpr ReduceLet(SExpr expr)
    {
      if (expr.Name != "let")
      {
        return expr;
      }

      var bindings = expr.Arguments[0].Arguments;
      var subexpr = expr.Arguments[1];

      var dict = new Dictionary<string, SExpr>();
      foreach (var binding in bindings)
      {
        Contract.Assert(binding.ArgCount == 1);
        dict.Add(binding.Name, binding.Arguments[0]);
      }

      Contract.Assert(!dict.ContainsKey(subexpr.Name));

      var workList = new Stack<SExpr>();
      workList.Push(subexpr);
      while (workList.Count > 0)
      {
        var curr = workList.Pop();
        for (int i = 0; i < curr.ArgCount; i++)
        {
          var arg = curr.Arguments[i];
          if (dict.ContainsKey(arg.Name))
          {
            curr.Arguments[i] = dict[arg.Name];
          }
          else
          {
            workList.Push(arg);
          }
        }
      }

      return subexpr;
    }

    protected static object ParseArrayFromProverResponse(SExpr resp)
    {
      resp = ReduceLet(resp);
      var dict = ParseArrayFromArrayExpr(resp);
      if (dict == null)
      {
        dict = ParseArrayFromProverLambdaExpr(resp);
      }

      if (dict == null)
      {
        return null;
      }

      var str = new StringWriter();
      str.Write("{");
      foreach (var entry in dict)
      {
        if (entry.Key != "*")
        {
          str.Write("\"{0}\":{1},", entry.Key, entry.Value);
        }
      }

      if (dict.ContainsKey("*"))
      {
        str.Write("\"*\":{0}", dict["*"]);
      }

      str.Write("}");
      return str.ToString();
    }

    private static Dictionary<string, object> ParseArrayFromProverLambdaExpr(SExpr resp)
    {
      var dict = new Dictionary<string, object>();
      if (resp.Name == "lambda" && resp.ArgCount == 2)
      {
        // TODO: multiple indices, as (lambda (() (x!1 Int) (x!2 Int)) ...)
        var indexVar = resp.Arguments[0].Arguments[0].Name;

        var cases = resp.Arguments[1];
        while (cases != null)
        {
          if (cases.Name == "ite")
          {
            var condition = cases.Arguments[0];
            var positive = cases.Arguments[1];
            var negative = cases.Arguments[2];

            // TODO: multiple index conditions, as (and (= x!1 5) (= x!2 3))
            // TODO: nested arrays, as (ite (...) (_ as-array k!5) (_ as-array k!3))

            if (condition.Name != "=")
            {
              throw new VCExprEvaluationException();
            }

            if (condition.Arguments[0].Name != indexVar)
            {
              throw new VCExprEvaluationException();
            }

            var index = ParseValueFromProver(condition.Arguments[1]);
            var value = ParseValueFromProver(positive);

            dict.Add(index.ToString(), value);

            cases = negative;
          }
          else if (cases.IsId)
          {
            var value = ParseValueFromProver(cases);
            dict.Add("*", value);
            cases = null;
          }
          else
          {
            throw new VCExprEvaluationException();
          }
        }
      }

      return dict.Count > 0 ? dict : null;
    }

    private static Dictionary<string, object> ParseArrayFromArrayExpr(SExpr resp)
    {
      var dict = new Dictionary<string, object>();
      var curr = resp;
      while (curr != null)
      {
        if (curr.Name == "store")
        {
          var ary = curr.Arguments[0];
          var indices = curr.Arguments.Skip(1).Take(curr.ArgCount - 2).Select(ParseValueFromProver).ToArray();
          var val = curr.Arguments[curr.ArgCount - 1];
          dict.Add(String.Join(",", indices), ParseValueFromProver(val));
          curr = ary;
        }
        else if (curr.Name == "" && curr.ArgCount == 2 && curr.Arguments[0].Name == "as")
        {
          var val = curr.Arguments[1];
          dict.Add("*", ParseValueFromProver(val));
          curr = null;
        }
        else
        {
          return null;
        }
      }

      return dict.Count > 0 ? dict : null;
    }

    protected void ReportCoveredElements(SExpr unsatCoreSExp) {
      if (libOptions.TrackVerificationCoverage && unsatCoreSExp.Name != "") {
        currentErrorHandler.AddCoveredElement(TrackedNodeComponent.ParseSolverString(unsatCoreSExp.Name.Substring("aux$$assume$$".Length)));
      }

      foreach (var arg in unsatCoreSExp.Arguments) {
        if (libOptions.TrackVerificationCoverage) {
          currentErrorHandler.AddCoveredElement(TrackedNodeComponent.ParseSolverString(arg.Name.Substring("aux$$assume$$".Length)));
        }
      }
    }

    protected List<string> ParseUnsatCore(string resp)
    {
      if (resp == "" || resp == "()")
      {
        return null;
      }

      if (resp[0] == '(')
      {
        resp = resp.Substring(1, resp.Length - 2);
      }

      return resp.Split(' ').ToList();
    }

    protected int ParseRCount(SExpr resp)
    {
      try
      {
        return int.Parse(resp[0].Name);
      }
      catch
      {
        // If anything goes wrong with parsing the response from the solver,
        // it's better to be able to continue, even with uninformative data.
        currentErrorHandler?.OnProverWarning($"Failed to parse resource count from solver. Got: {resp}");
        return -1;
      }
    }

    public override void Push()
    {
      SendThisVC("(push 1)");
      DeclCollector.Push();
    }
  }

  public class SMTLibProverContext : DeclFreeProverContext
  {
    internal SMTLibProcessTheoremProver parent;
    
    public readonly HashSet<DatatypeTypeCtorDecl> KnownDatatypes = new HashSet<DatatypeTypeCtorDecl>();
    
    public readonly Dictionary<Function, VCExprNAry> DefinedFunctions = new Dictionary<Function, VCExprNAry>();

    public SMTLibProverContext(VCExpressionGenerator gen,
      VCGenerationOptions genOptions, SMTLibOptions options)
      : base(gen, genOptions, options)
    {
    }

    protected SMTLibProverContext(SMTLibProverContext par)
      : base(par)
    {
    }

    public override object Clone()
    {
      return new SMTLibProverContext(this);
    }

    public override string Lookup(VCExprVar var)
    {
      VCExprVar v = parent.AxBuilder?.TryTyped2Untyped(var);
      if (v != null)
      {
        var = v;
      }

      return parent.Namer.GetOriginalName(parent.Namer.Lookup(var));
    }

    public override void DeclareFunction(Function f, string attributes)
    {
      if (f.DefinitionBody != null)
      {
        DefinedFunctions.Add(f, (VCExprNAry) translator.Translate(f.DefinitionBody));
      }

      base.DeclareFunction(f, attributes);
    }

    public override void DeclareType(TypeCtorDecl t, string attributes)
    {
      if (t is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        if (datatypeTypeCtorDecl.Arity > 0)
        {
          throw new ProverException("Polymorphic datatypes are not supported");
        }
        KnownDatatypes.Add(datatypeTypeCtorDecl);
      }
      base.DeclareType(t, attributes);
    }

    // Return the datatype of the given name if there is one, null otherwise.
    public DatatypeTypeCtorDecl LookupDatatype(string name)
    {
      foreach (var datatype in KnownDatatypes)
      {
        if (name == datatype.ToString())
        {
          return datatype;
        }
      }

      return null;
    }
  }

  public class Factory : ProverFactory
  {
    public override ProverInterface SpawnProver(SMTLibOptions libOptions, ProverOptions options, object ctxt)
    {
      //Contract.Requires(ctxt != null);
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      return this.SpawnProver(libOptions, options,
        Cce.NonNull((SMTLibProverContext) ctxt).ExprGen,
        Cce.NonNull((SMTLibProverContext) ctxt));
    }

    public override ProverContext NewProverContext(ProverOptions options)
    {
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      VCExpressionGenerator gen = new VCExpressionGenerator();
      List<string> /*!>!*/
        proverCommands = new List<string /*!*/>();
      proverCommands.Add("smtlib");
      var opts = (SMTLibSolverOptions) options;
      if (opts.Solver == SolverKind.Z3)
      {
        proverCommands.Add("z3");
      }
      else
      {
        proverCommands.Add("external");
      }

      VCGenerationOptions genOptions = new VCGenerationOptions(options.LibOptions, proverCommands);
      return new SMTLibProverContext(gen, genOptions, options.LibOptions);
    }

    public override ProverOptions BlankProverOptions(SMTLibOptions libOptions)
    {
      return new SMTLibSolverOptions(libOptions);
    }

    protected virtual SMTLibProcessTheoremProver SpawnProver(SMTLibOptions libOptions, ProverOptions options,
      VCExpressionGenerator gen,
      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Ensures(Contract.Result<SMTLibProcessTheoremProver>() != null);
      if (options.BatchMode) {
        return new SMTLibBatchTheoremProver(libOptions, (SMTLibSolverOptions)options, gen, ctx);
      } else {
        return new SMTLibInteractiveTheoremProver(libOptions, (SMTLibSolverOptions)options, gen, ctx);
      }
    }
  }
}
