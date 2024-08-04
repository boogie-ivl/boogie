using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class MonomorphismChecker : ReadOnlyVisitor
  {
    // This visitor checks if the program is already monomorphic.

    public static bool DoesTypeCtorDeclNeedMonomorphization(TypeCtorDecl typeCtorDecl)
    {
      return typeCtorDecl.Arity > 0 && (typeCtorDecl as ICarriesAttributes).FindStringAttribute("builtin") == null;
    }

    public static bool IsMonomorphic(Program program)
    {
      var checker = new MonomorphismChecker();
      checker.VisitProgram(program);
      return checker.isMonomorphic;
    }
    
    bool isMonomorphic;

    private MonomorphismChecker()
    {
      isMonomorphic = true;
    }
    
    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitDeclWithFormals(node);
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitBinderExpr(node);
    }

    public override Type VisitMapType(MapType node)
    {
      if (node.TypeParameters.Count > 0)
      {
        isMonomorphic = false;
      }
      return base.VisitMapType(node);
    }

    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      if (DoesTypeCtorDeclNeedMonomorphization(node))
      {
        isMonomorphic = false;
      }
      return base.VisitTypeCtorDecl(node);
    }
  }

  class TypeDependencyVisitor : ReadOnlyVisitor
  {
    /*
     * An instance of this visitor is created with a type variable "formal" (passed to the constructor).
     * This visitor walks over a type T and adds an edge from any type variable nested inside T
     * to the type variable "formal". The class MonomorphizableChecker uses this visitor to check
     * that there are no expanding type cycles when a polymorphic function calls another
     * polymorphic function or a polymorphic procedure calls another polymorphic procedure.
     */

    private Graph<TypeVariable> typeVariableDependencyGraph;
    private HashSet<Tuple<TypeVariable, TypeVariable>> strongDependencyEdges;
    private TypeVariable formal;
    private int insideContructedType;
    
    public TypeDependencyVisitor(Graph<TypeVariable> typeVariableDependencyGraph,
      HashSet<Tuple<TypeVariable, TypeVariable>> strongDependencyEdges, TypeVariable formal)
    {
      this.typeVariableDependencyGraph = typeVariableDependencyGraph;
      this.strongDependencyEdges = strongDependencyEdges;
      this.formal = formal;
      insideContructedType = 0;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      insideContructedType++;
      base.VisitCtorType(node);
      insideContructedType--;
      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      insideContructedType++;
      base.VisitMapType(node);
      insideContructedType--;
      return node;
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      typeVariableDependencyGraph.AddEdge(node, formal);
      if (insideContructedType > 0)
      {
        strongDependencyEdges.Add(new Tuple<TypeVariable, TypeVariable>(node, formal));
      }
      return base.VisitTypeVariable(node);
    }
  }

  public enum MonomorphizableStatus
  {
    UnhandledPolymorphism,
    ExpandingTypeCycle,
    Monomorphizable,
  }
  
  class MonomorphizableChecker : ReadOnlyVisitor
  {
    /*
     * This visitor checks if the program is monomorphizable. It calculates one status value from
     * the enum MonomorphizableStatus for the program.
     */
    public static MonomorphizableStatus IsMonomorphizable(Program program, out HashSet<Axiom> polymorphicFunctionAxioms)
    {
      var checker = new MonomorphizableChecker(program);
      checker.VisitProgram(program);
      polymorphicFunctionAxioms = checker.polymorphicFunctionAxioms;
      if (!checker.isMonomorphizable)
      {
        return MonomorphizableStatus.UnhandledPolymorphism;
      }
      if (!checker.IsFinitelyInstantiable())
      {
        return MonomorphizableStatus.ExpandingTypeCycle;
      }
      return MonomorphizableStatus.Monomorphizable;
    }
    
    private bool isMonomorphizable;
    private HashSet<Axiom> polymorphicFunctionAxioms;
    private Graph<TypeVariable> typeVariableDependencyGraph; // (T,U) in this graph iff T flows to U
    private HashSet<Tuple<TypeVariable, TypeVariable>> strongDependencyEdges; // (T,U) in this set iff a type constructed from T flows into U

    private MonomorphizableChecker(Program program)
    {
      isMonomorphizable = true;
      polymorphicFunctionAxioms = program.TopLevelDeclarations.OfType<Function>()
        .Where(f => f.TypeParameters.Count > 0 && f.DefinitionAxiom != null)
        .Select(f => f.DefinitionAxiom).ToHashSet();
      typeVariableDependencyGraph = new Graph<TypeVariable>();
      strongDependencyEdges = new HashSet<Tuple<TypeVariable, TypeVariable>>();
    }

    private bool IsFinitelyInstantiable()
    {
      var sccs = new StronglyConnectedComponents<TypeVariable>(typeVariableDependencyGraph.Nodes,
        typeVariableDependencyGraph.Predecessors, typeVariableDependencyGraph.Successors);
      sccs.Compute();
      foreach (var scc in sccs)
      {
        foreach (var edge in strongDependencyEdges)
        {
          if (scc.Contains(edge.Item1) && scc.Contains(edge.Item2))
          {
            return false;
          }
        }
      }
      return true;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is FunctionCall functionCall)
      {
        functionCall.Func.TypeParameters.ForEach(t =>
        {
          var visitor = new TypeDependencyVisitor(typeVariableDependencyGraph, strongDependencyEdges, t);
          visitor.Visit(node.TypeParameters[t]);
        });
      }
      Visit(node.Type);
      return base.VisitNAryExpr(node);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      node.Proc.TypeParameters.ForEach(t =>
      {
        var visitor = new TypeDependencyVisitor(typeVariableDependencyGraph, strongDependencyEdges, t);
        visitor.Visit(node.TypeParameters[t]);
      });
      return base.VisitCallCmd(node);
    }

    public override Function VisitFunction(Function node)
    {
      if (polymorphicFunctionAxioms.Contains(node.DefinitionAxiom))
      {
        var forallExpr = (ForallExpr) node.DefinitionAxiom.Expr;
        node.TypeParameters.Zip(forallExpr.TypeParameters)
          .ForEach(x => typeVariableDependencyGraph.AddEdge(x.First, x.Second));
        VisitExpr(forallExpr.Body);
      }
      return base.VisitFunction(node);
    }

    public override Implementation VisitImplementation(Implementation node)
    {
      node.Proc.TypeParameters.Zip(node.TypeParameters)
        .ForEach(x => typeVariableDependencyGraph.AddEdge(x.First, x.Second));
      return base.VisitImplementation(node);
    }

    public override Absy Visit(Absy node)
    {
      if (node is ICarriesAttributes attrNode && attrNode.Attributes != null)
      {
        VisitQKeyValue(attrNode.Attributes);
      }
      return base.Visit(node);
    }
    
    public override Type VisitTypeProxy(TypeProxy node)
    {
      if (node.ProxyFor == null)
      {
        isMonomorphizable = false;
      }
      else
      {
        Visit(TypeProxy.FollowProxy(node));
      }
      return node;
    }

    public override Type VisitBvTypeProxy(BvTypeProxy node)
    {
      if (node.ProxyFor == null)
      {
        isMonomorphizable = false;
      }
      else
      {
        Visit(TypeProxy.FollowProxy(node));
      }
      return node;
    }

    public override Expr VisitBvConcatExpr(BvConcatExpr node)
    {
      Visit(node.Type);
      return base.VisitBvConcatExpr(node);
    }

    public override Expr VisitBvExtractExpr(BvExtractExpr node)
    {
      Visit(node.Type);
      return base.VisitBvExtractExpr(node);
    }
  }

  class InstantiationHintCollector : ReadOnlyVisitor
  {
    /*
     * This visitor walks over a polymorphic quantifier to collect hints for instantiating its type parameters
     * in the field instantiationHints. This field maps each type parameter T of the quantifier to a dictionary
     * that maps a polymorphic type/function/map D to a set of integers, such that each integer in the set is a
     * valid position in the list of type parameters of D. If position i is in the list corresponding to D,
     * then the concrete type at position i among instances of D is a hint for T.
     */
    
    private HashSet<TypeVariable> typeParameters;
    private Dictionary<TypeVariable, Dictionary<Absy, HashSet<int>>> instantiationHints;

    public static Dictionary<TypeVariable, Dictionary<Absy, HashSet<int>>> CollectInstantiationHints(QuantifierExpr quantifierExpr)
    {
      var instantiationHintCollector = new InstantiationHintCollector(quantifierExpr);
      instantiationHintCollector.VisitExpr(quantifierExpr);
      return instantiationHintCollector.instantiationHints;
    }

    private InstantiationHintCollector(QuantifierExpr quantifierExpr)
    {
      typeParameters = new HashSet<TypeVariable>(quantifierExpr.TypeParameters);
      instantiationHints = quantifierExpr.TypeParameters.ToDictionary(typeParameter => typeParameter,
        _ => new Dictionary<Absy, HashSet<int>>());
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is MapSelect or MapStore)
      {
        var actualTypeParams = node.TypeParameters.FormalTypeParams.Select(x => node.TypeParameters[x]).ToList();
        PopulateInstantiationHints(actualTypeParams, node.Args[0].Type);
      }
      else if (node.Fun is FunctionCall functionCall && functionCall.Func is not DatatypeConstructor)
      {
        var actualTypeParams = node.TypeParameters.FormalTypeParams.Select(x => node.TypeParameters[x]).ToList();
        PopulateInstantiationHints(actualTypeParams, functionCall.Func);
      }
      return base.VisitNAryExpr(node);
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      PopulateInstantiationHints(node.Arguments, node.Decl);
      return base.VisitCtorType(node);
    }

    private void PopulateInstantiationHints(List<Type> actualTypeParams, Absy decl)
    {
      for (int i = 0; i < actualTypeParams.Count; i++)
      {
        if (actualTypeParams[i] is TypeVariable typeVariable && typeParameters.Contains(typeVariable))
        {
          if (!instantiationHints[typeVariable].ContainsKey(decl))
          {
            instantiationHints[typeVariable][decl] = new HashSet<int>();
          }
          instantiationHints[typeVariable][decl].Add(i);
        }
      }
    }
  }

  abstract class BinderExprMonomorphizer
  {
    /*
     * This is the abstract class that is extended by classes for monomorphizing
     * LambdaExpr, ForallExpr, and ExistsExpr.
     */

    protected MonomorphizationVisitor monomorphizationVisitor;
    protected Dictionary<List<Type>, Expr> instanceExprs { get; }

    protected BinderExprMonomorphizer(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      instanceExprs = new Dictionary<List<Type>, Expr>(new ListComparer<Type>());
    }

    // Returns the BinderExpr for which this instance of BinderExprMonomorphizer was created.
    public abstract BinderExpr BinderExpr { get; }

    // Instantiates this.BinderExpr using the known function and type instantiations.
    // Returns true if fresh instances of this.BinderExpr were created.
    public abstract bool Instantiate();

    // Returns the monomorphized version of this.BinderExpr.
    public abstract Expr MonomorphicExpr(PolymorphicMapAndBinderSubstituter substituter);
  }

  class LambdaExprMonomorphizer : BinderExprMonomorphizer
  {
    private LambdaExpr lambdaExpr;

    public LambdaExprMonomorphizer(LambdaExpr lambdaExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(monomorphizationVisitor)
    {
      this.lambdaExpr = lambdaExpr;
    }

    public override BinderExpr BinderExpr => lambdaExpr;

    public override bool Instantiate()
    {
      var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(lambdaExpr.Type);
      Debug.Assert(instanceExprs.Count <= polymorphicMapInfo.Instances.Count);
      if (instanceExprs.Count == polymorphicMapInfo.Instances.Count)
      {
        return false;
      }
      polymorphicMapInfo.Instances.Skip(instanceExprs.Count).ForEach(x =>
        instanceExprs[x] = monomorphizationVisitor.InstantiateBinderExpr(lambdaExpr, x));
      return true;
    }

    public override Expr MonomorphicExpr(PolymorphicMapAndBinderSubstituter substituter)
    {
      return substituter.VisitExpr(monomorphizationVisitor.RegisterPolymorphicMapType(lambdaExpr.Type)
        .GetLambdaConstructor(instanceExprs));
    }
  }

  abstract class QuantifierExprMonomorphizer : BinderExprMonomorphizer
  {
    private QuantifierExpr quantifierExpr;
    private Dictionary<TypeVariable, Dictionary<Absy, HashSet<int>>> instantiationHints;

    protected QuantifierExprMonomorphizer(QuantifierExpr quantifierExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(monomorphizationVisitor)
    {
      this.quantifierExpr = quantifierExpr;
      instantiationHints = InstantiationHintCollector.CollectInstantiationHints(quantifierExpr);
    }

    public override BinderExpr BinderExpr => quantifierExpr;

    public override bool Instantiate()
    {
      var instanceExprsCount = instanceExprs.Count;
      var typeParameterIndexToTypeHints = Enumerable.Range(0, quantifierExpr.TypeParameters.Count)
        .Select(_ => new HashSet<Type>()).ToList();
      for (int typeParameterIndex = 0; typeParameterIndex < quantifierExpr.TypeParameters.Count; typeParameterIndex++)
      {
        var typeParameter = quantifierExpr.TypeParameters[typeParameterIndex];
        foreach (var (decl, actualIndexes) in instantiationHints[typeParameter])
        {
          foreach (var actualTypeParameters in monomorphizationVisitor.AbsyInstantiations(decl))
          {
            foreach (var actualIndex in actualIndexes)
            {
              typeParameterIndexToTypeHints[typeParameterIndex].Add(actualTypeParameters[actualIndex]);
            }
          }
        }
      }
      InstantiateOne(typeParameterIndexToTypeHints, new List<Type>());
      return instanceExprsCount < instanceExprs.Count;
    }

    private void InstantiateOne(List<HashSet<Type>> typeParameterIndexToTypeHints, List<Type> actualTypeParams)
    {
      if (typeParameterIndexToTypeHints.Count == actualTypeParams.Count)
      {
        if (!instanceExprs.ContainsKey(actualTypeParams))
        {
          instanceExprs[new List<Type>(actualTypeParams)] =
            monomorphizationVisitor.InstantiateBinderExpr(quantifierExpr, actualTypeParams);
        }
        return;
      }

      foreach (var type in typeParameterIndexToTypeHints[actualTypeParams.Count])
      {
        var addPosition = actualTypeParams.Count;
        actualTypeParams.Add(type);
        InstantiateOne(typeParameterIndexToTypeHints, actualTypeParams);
        actualTypeParams.RemoveAt(addPosition);
      }
    }
  }

  class ForallExprMonomorphizer : QuantifierExprMonomorphizer
  {
    public ForallExprMonomorphizer(ForallExpr forallExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(forallExpr, monomorphizationVisitor)
    {
    }

    public override Expr MonomorphicExpr(PolymorphicMapAndBinderSubstituter substituter)
    {
      return Expr.And(instanceExprs.Values.Select(x => substituter.VisitExpr(x)));
    }
  }

  class ExistsExprMonomorphizer : QuantifierExprMonomorphizer
  {
    public ExistsExprMonomorphizer(ExistsExpr existsExpr, MonomorphizationVisitor monomorphizationVisitor) :
      base(existsExpr, monomorphizationVisitor)
    {
    }

    public override Expr MonomorphicExpr(PolymorphicMapAndBinderSubstituter substituter)
    {
      return Expr.Or(instanceExprs.Values.Select(x => substituter.VisitExpr(x)));
    }
  }

  class PolymorphicMapInfo
  {
    /*
     * An instance of this class is created for each polymorphic map type.
     * This class implements the instantiation of the polymorphic map type
     * for concrete instances encountered in the program. This class also
     * creates the datatype that represents the polymorphic map type in the
     * monomorphized program.
     */

    class FieldInfo
    {
      public Type type;

      public int index;

      // actualParameters is the original parameter list that created this instance of FieldInfo
      public List<Type> actualParameters;

      public FieldInfo(Type type, int index, List<Type> actualParameters)
      {
        this.type = type;
        this.index = index;
        this.actualParameters = actualParameters;
      }
    }

    private MonomorphizationVisitor monomorphizationVisitor;
    private MapType mapType;
    private Dictionary<List<Type>, FieldInfo> fieldInfos;
    private List<List<Type>> instances;
    private DatatypeTypeCtorDecl datatypeTypeCtorDecl;

    public PolymorphicMapInfo(MonomorphizationVisitor monomorphizationVisitor, MapType mapType)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.mapType = mapType;
      fieldInfos = new Dictionary<List<Type>, FieldInfo>(new ListComparer<Type>());
      instances = new List<List<Type>>();
      datatypeTypeCtorDecl = new DatatypeTypeCtorDecl(new TypeCtorDecl(Token.NoToken, MapTypeName, 0,
        new QKeyValue(Token.NoToken, "datatype", new List<object>(), null)));
    }

    public CtorType Datatype => new(Token.NoToken, datatypeTypeCtorDecl, new List<Type>());

    public List<List<Type>> Instances => instances;

    public DatatypeTypeCtorDecl CreateDatatypeTypeCtorDecl(PolymorphicMapAndBinderSubstituter polymorphicMapAndBinderSubstituter)
    {
      var inParams = instances.Select(x => new Formal(Token.NoToken,
        new TypedIdent(Token.NoToken, FieldName(x), polymorphicMapAndBinderSubstituter.VisitType(fieldInfos[x].type)),
        true)).ToList<Variable>();
      var outParam = new Formal(Token.NoToken,
        new TypedIdent(Token.NoToken, MapTypeName, new CtorType(Token.NoToken, datatypeTypeCtorDecl, new List<Type>())),
        false);
      var function = new Function(Token.NoToken, MapTypeName, new List<TypeVariable>(), inParams, outParam, null,
        new QKeyValue(Token.NoToken, "constructor", new List<object>(), null));
      var constructor = new DatatypeConstructor(function);
      datatypeTypeCtorDecl.AddConstructor(constructor);
      return datatypeTypeCtorDecl;
    }

    public Expr GetLambdaConstructor(Dictionary<List<Type>, Expr> instanceExprs)
    {
      var returnExpr = new NAryExpr(Token.NoToken, new FunctionCall(datatypeTypeCtorDecl.Constructors[0]),
        instances.Select(x => instanceExprs[x]).ToList());
      returnExpr.Type = Datatype;
      returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      return returnExpr;
    }

    public FieldAccess GetFieldAccess(List<Type> actualParameters)
    {
      Debug.Assert(fieldInfos.ContainsKey(actualParameters));
      actualParameters = PopulateField(actualParameters);
      return new FieldAccess(Token.NoToken, FieldName(actualParameters), datatypeTypeCtorDecl,
        new List<DatatypeAccessor> { new(0, fieldInfos[actualParameters].index) });
    }

    public Type GetFieldType(List<Type> actualParameters)
    {
      actualParameters = PopulateField(actualParameters);
      return fieldInfos[actualParameters].type;
    }

    public List<Type> PopulateField(List<Type> actualParameters)
    {
      if (!fieldInfos.ContainsKey(actualParameters))
      {
        fieldInfos[actualParameters] = new FieldInfo(Instantiate(actualParameters), instances.Count, actualParameters);
        instances.Add(actualParameters);
      }
      return fieldInfos[actualParameters].actualParameters;
    }

    private string MapTypeName => $"PolymorphicMapType_{mapType.UniqueId}";

    private string FieldName(List<Type> actualParameters)
    {
      return MonomorphizationVisitor.MkInstanceName(MapTypeName, actualParameters);
    }

    private MapType Instantiate(List<Type> actualParameters)
    {
      var subst = mapType.TypeParameters.MapTo(actualParameters);
      List<Type> newArgs = new List<Type>();
      foreach (Type t in mapType.Arguments)
      {
        newArgs.Add(t.Substitute(subst));
      }
      Type newResult = mapType.Result.Substitute(subst);
      var returnType = new MapType(mapType.tok, new List<TypeVariable>(), newArgs, newResult);
      return (MapType)new MonomorphizationDuplicator(monomorphizationVisitor).VisitMapType(returnType);
    }
  }

  class PolymorphicMapAndBinderSubstituter : VarDeclOnceStandardVisitor
  {
    /*
     * This visitor finalizes the monomorphization of polymorphic maps and binders once
     * all instantiations have been discovered. It accomplishes the following substitutions:
     * - ach access to a polymorphic map with an access to corresponding datatype
     * - each occurrence of a polymorphic map type with the corresponding datatype
     * - each polymorphic lambda with a constructor call of the corresponding datatype
     * - each polymorphic forall quantifier with a conjunction
     * - each polymorphic exists quantifier with a disjunction
     */
    
    private MonomorphizationVisitor monomorphizationVisitor;
    private Dictionary<BinderExpr, BinderExprMonomorphizer> binderExprMonomorphizers;
    // The top-level conjuncts of the rewritten axiom are added to this list, thus allowing 
    // the original axioms to be replaced by the axioms collected in splitAxioms. Splitting 
    // the axioms makes it easy to read the rewritten program and enables axiom pruning to 
    // be applied.
    private List<Axiom> splitAxioms;

    public PolymorphicMapAndBinderSubstituter(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      splitAxioms = new List<Axiom>();
    }

    public List<Axiom> Substitute(Program program)
    {
      binderExprMonomorphizers = monomorphizationVisitor.GetBinderExprMonomorphizers();
      Visit(program);
      return splitAxioms;
    }

    private List<Type> ActualTypeParams(TypeParamInstantiation typeParamInstantiation)
    {
      return typeParamInstantiation.FormalTypeParams.Select(x => TypeProxy.FollowProxy(typeParamInstantiation[x]))
        .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
    }

    public override Axiom VisitAxiom(Axiom node)
    {
      var axiom = base.VisitAxiom(node);
      var stack = new Stack<Expr>();
      stack.Push(axiom.Expr);
      while (stack.Count > 0)
      {
        var expr = stack.Pop();
        if (expr is NAryExpr { Fun: BinaryOperator { Op: BinaryOperator.Opcode.And } } nAryExpr)
        {
          stack.Push(nAryExpr.Args[0]);
          stack.Push(nAryExpr.Args[1]);
        }
        else
        {
          var newAxiom = new Axiom(axiom.tok, expr);
          if (monomorphizationVisitor.originalAxiomToSplitAxioms.ContainsKey(axiom)) {
            monomorphizationVisitor.originalAxiomToSplitAxioms[axiom].Add(newAxiom);
          }
          splitAxioms.Add(newAxiom);
        }
      }
      return axiom;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      if (node.Fun is BinaryOperator { Op: BinaryOperator.Opcode.Eq } && !node.Args[0].Type.Equals(node.Args[1].Type))
      {
        return Expr.False;
      }
      if (node.Fun is BinaryOperator { Op: BinaryOperator.Opcode.Neq } && !node.Args[0].Type.Equals(node.Args[1].Type))
      {
        return Expr.True;
      }
      if (!(node.Fun is MapSelect || node.Fun is MapStore) || node.TypeParameters.FormalTypeParams.Count == 0)
      {
        return base.VisitNAryExpr(node);
      }
      var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(node.Args[0].Type);
      node = (NAryExpr)base.VisitNAryExpr(node);
      var actualTypeParams = ActualTypeParams(node.TypeParameters);
      var fieldAccess = polymorphicMapInfo.GetFieldAccess(actualTypeParams);
      var polymorphicMapDatatypeExpr = node.Args[0];
      var fieldAccessExpr = new NAryExpr(Token.NoToken, fieldAccess, new List<Expr> { polymorphicMapDatatypeExpr });
      fieldAccessExpr.Type = polymorphicMapInfo.GetFieldType(actualTypeParams);
      fieldAccessExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      node.Args[0] = fieldAccessExpr;
      node.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      if (node.Fun is MapStore)
      {
        node.Type = fieldAccessExpr.Type;
        var fieldUpdate = new FieldUpdate(fieldAccess);
        node = new NAryExpr(Token.NoToken, fieldUpdate, new List<Expr> { polymorphicMapDatatypeExpr, node });
        node.Type = polymorphicMapInfo.Datatype;
      }
      return node;
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(node.Map.Type);
      var mapAssignLhs = (MapAssignLhs)base.VisitMapAssignLhs(node);
      if (mapAssignLhs.TypeParameters.FormalTypeParams.Count > 0)
      {
        var actualTypeParams = ActualTypeParams(mapAssignLhs.TypeParameters);
        var fieldAccess = polymorphicMapInfo.GetFieldAccess(actualTypeParams);
        var fieldAssignLhs = new FieldAssignLhs(Token.NoToken, mapAssignLhs.Map, fieldAccess)
        {
          TypeParameters = SimpleTypeParamInstantiation.EMPTY
        };
        mapAssignLhs = new MapAssignLhs(mapAssignLhs.tok, fieldAssignLhs, mapAssignLhs.Indexes)
        {
          TypeParameters = SimpleTypeParamInstantiation.EMPTY
        };
      }
      else
      {
        mapAssignLhs = new MapAssignLhs(mapAssignLhs.tok, mapAssignLhs.Map, mapAssignLhs.Indexes)
        {
          TypeParameters = SimpleTypeParamInstantiation.EMPTY
        };
      }
      return mapAssignLhs;
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      var fieldAssignLhs = (FieldAssignLhs)base.VisitFieldAssignLhs(node);
      fieldAssignLhs = new FieldAssignLhs(node.tok, fieldAssignLhs.Datatype, fieldAssignLhs.FieldAccess)
        {
          TypeParameters = SimpleTypeParamInstantiation.EMPTY
        };
      return fieldAssignLhs;
    }

    public override Type VisitMapType(MapType node)
    {
      node = (MapType)base.VisitMapType(node);
      if (node.TypeParameters.Count > 0)
      {
        var polymorphicMapInfo = monomorphizationVisitor.RegisterPolymorphicMapType(node);
        return polymorphicMapInfo.Datatype;
      }
      return node;
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      var returnExpr = binderExprMonomorphizers.ContainsKey(node)
        ? binderExprMonomorphizers[node].MonomorphicExpr(this)
        : base.VisitBinderExpr(node);
      if (returnExpr is QuantifierExpr { Triggers: { } } quantifierExpr)
      {
        quantifierExpr.Triggers = VisitTrigger(quantifierExpr.Triggers);
      }
      if (returnExpr is BinderExpr { Attributes: { } } binderExpr)
      {
        binderExpr.Attributes = VisitQKeyValue(binderExpr.Attributes);
      }
      return returnExpr;
    }

    public override Expr VisitLambdaExpr(LambdaExpr node)
    {
      return VisitBinderExpr(node);
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      return VisitBinderExpr(node);
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      return VisitBinderExpr(node);
    }

    public override Type VisitType(Type node)
    {
      return (Type)Visit(node);
    }

    public override Type VisitBasicType(BasicType node)
    {
      return node;
    }

    public override Type VisitFloatType(FloatType node)
    {
      return node;
    }

    public override Type VisitBvType(BvType node)
    {
      return node;
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      return node;
    }

    public override Expr VisitExpr(Expr node)
    {
      node = base.VisitExpr(node);
      node.Type = VisitType(node.Type);
      return node;
    }
    
    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      var identifierExpr = base.VisitIdentifierExpr(node);
      identifierExpr.Type = VisitType(identifierExpr.Type);
      return identifierExpr;
    }
    
    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      node.Body = VisitType(node.Body);
      return node;
    }

    public override Constant VisitConstant(Constant node)
    {
      return (Constant)VisitVariable(node);
    }
  }

  class MonomorphizationDuplicator : Duplicator
  {
    // This class works together with MonomorphizationVisitor to accomplish monomorphization
    // of a Boogie program.

    private MonomorphizationVisitor monomorphizationVisitor;
    private Dictionary<TypeVariable, Type> typeParamInstantiation;
    private Dictionary<Variable, Variable> variableMapping;
    private Dictionary<Variable, Variable> boundVarSubst;

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      typeParamInstantiation = new Dictionary<TypeVariable, Type>();
      variableMapping = new Dictionary<Variable, Variable>();
      boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor,
      Dictionary<TypeVariable, Type> typeParamInstantiation)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.typeParamInstantiation = typeParamInstantiation;
      variableMapping = new Dictionary<Variable, Variable>();
      boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public MonomorphizationDuplicator(MonomorphizationVisitor monomorphizationVisitor,
      Dictionary<TypeVariable, Type> typeParamInstantiation, Dictionary<Variable, Variable> variableMapping)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
      this.typeParamInstantiation = typeParamInstantiation;
      this.variableMapping = variableMapping;
      boundVarSubst = new Dictionary<Variable, Variable>();
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      var fieldAssignLhs = (FieldAssignLhs)base.VisitFieldAssignLhs(node);
      var actualTypeParams =
        fieldAssignLhs.TypeParameters.FormalTypeParams.Select(x =>
            TypeProxy.FollowProxy(fieldAssignLhs.TypeParameters[x]).Substitute(typeParamInstantiation))
          .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
      fieldAssignLhs.TypeParameters =
        SimpleTypeParamInstantiation.From(fieldAssignLhs.TypeParameters.FormalTypeParams, actualTypeParams);
      if (actualTypeParams.Any(HasFreeTypeVariables))
      {
        return fieldAssignLhs;
      }
      var fieldAccess = fieldAssignLhs.FieldAccess;
      var datatypeTypeCtorDecl = fieldAccess.DatatypeTypeCtorDecl;
      if (datatypeTypeCtorDecl.Arity == 0)
      {
        monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
      }
      else
      {
        fieldAssignLhs.FieldAccess =
          monomorphizationVisitor.InstantiateFieldAccess(fieldAssignLhs.FieldAccess, actualTypeParams);
      }
      return fieldAssignLhs;
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      var mapAssignLhs = (MapAssignLhs)base.VisitMapAssignLhs(node);
      var actualTypeParams =
        mapAssignLhs.TypeParameters.FormalTypeParams.Select(x =>
            TypeProxy.FollowProxy(mapAssignLhs.TypeParameters[x]).Substitute(typeParamInstantiation))
          .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
      mapAssignLhs.TypeParameters =
        SimpleTypeParamInstantiation.From(mapAssignLhs.TypeParameters.FormalTypeParams, actualTypeParams);
      if (!actualTypeParams.Any(HasFreeTypeVariables) && actualTypeParams.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(node.Map.Type).PopulateField(actualTypeParams);
      }
      return mapAssignLhs;
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      var returnExpr = (NAryExpr)base.VisitNAryExpr(node);
      returnExpr.Type = VisitType(node.Type);
      var actualTypeParams =
        returnExpr.TypeParameters.FormalTypeParams.Select(x =>
            TypeProxy.FollowProxy(returnExpr.TypeParameters[x]).Substitute(typeParamInstantiation))
          .Select(x => monomorphizationVisitor.LookupType(x)).ToList();
      returnExpr.TypeParameters =
        SimpleTypeParamInstantiation.From(returnExpr.TypeParameters.FormalTypeParams, actualTypeParams);
      if (returnExpr.Fun is TypeCoercion)
      {
        return returnExpr.Args[0];
      }

      if (actualTypeParams.Any(HasFreeTypeVariables))
      {
        return returnExpr;
      }
      
      if (returnExpr.Fun is MapSelect or MapStore && returnExpr.TypeParameters.FormalTypeParams.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(returnExpr.Args[0].Type).PopulateField(actualTypeParams);
      }
      else if (returnExpr.Fun is IsConstructor isConstructor)
      {
        var datatypeTypeCtorDecl = isConstructor.DatatypeTypeCtorDecl;
        if (datatypeTypeCtorDecl.Arity == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
        }
        else
        {
          returnExpr.Fun = monomorphizationVisitor.InstantiateIsConstructor(isConstructor, actualTypeParams);
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }
      else if (returnExpr.Fun is FieldAccess fieldAccess)
      {
        var datatypeTypeCtorDecl = fieldAccess.DatatypeTypeCtorDecl;
        if (datatypeTypeCtorDecl.Arity == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
        }
        else
        {
          returnExpr.Fun = monomorphizationVisitor.InstantiateFieldAccess(fieldAccess, actualTypeParams);
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }
      else if (returnExpr.Fun is FieldUpdate fieldUpdate)
      {
        var datatypeTypeCtorDecl = fieldUpdate.DatatypeTypeCtorDecl;
        if (datatypeTypeCtorDecl.Arity == 0)
        {
          monomorphizationVisitor.VisitTypeCtorDecl(datatypeTypeCtorDecl);
        }
        else
        {
          returnExpr.Fun = monomorphizationVisitor.InstantiateFieldUpdate(fieldUpdate, actualTypeParams);
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }
      else if (returnExpr.Fun is FunctionCall functionCall)
      {
        // a non-polymorphic function must be processed to rewrite any polymorphic types it uses
        // to the corresponding instantiated types
        if (functionCall.Func.TypeParameters.Count == 0)
        {
          if (functionCall.Func is DatatypeConstructor constructor)
          {
            monomorphizationVisitor.VisitTypeCtorDecl(constructor.datatypeTypeCtorDecl);
          }
          else
          {
            monomorphizationVisitor.VisitFunction(functionCall.Func);
          }
          returnExpr.Fun = new FunctionCall(functionCall.Func);
        }
        else
        {
          if (functionCall.Func is DatatypeConstructor constructor)
          {
            var datatypeTypeCtorDecl =
              (DatatypeTypeCtorDecl)monomorphizationVisitor.InstantiateTypeCtorDecl(constructor.datatypeTypeCtorDecl,
                actualTypeParams);
            returnExpr.Fun = new FunctionCall(datatypeTypeCtorDecl.Constructors[constructor.index]);
          }
          else
          {
            returnExpr.Fun =
              new FunctionCall(monomorphizationVisitor.InstantiateFunction(functionCall.Func, actualTypeParams));
          }
          returnExpr.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        }
      }

      return returnExpr;
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      var returnCallCmd = (CallCmd)base.VisitCallCmd(node);
      if (returnCallCmd.Proc.TypeParameters.Count > 0)
      {
        var actualTypeParams =
          returnCallCmd.TypeParameters.FormalTypeParams.Select(x =>
              TypeProxy.FollowProxy(returnCallCmd.TypeParameters[x]).Substitute(typeParamInstantiation))
            .Select(monomorphizationVisitor.LookupType).ToList();
        returnCallCmd.Proc = monomorphizationVisitor.InstantiateProcedure(node.Proc, actualTypeParams);
        returnCallCmd.callee = returnCallCmd.Proc.Name;
        returnCallCmd.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        monomorphizationVisitor.InlineCallCmd(node, actualTypeParams);
      }
      return returnCallCmd;
    }

    public override Type VisitTypeVariable(TypeVariable node)
    {
      if (typeParamInstantiation.ContainsKey(node))
      {
        return typeParamInstantiation[node];
      }
      return node;
    }

    public override Type VisitMapType(MapType node)
    {
      node = (MapType)node.Clone();
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        node.Arguments[i] = (Type)Visit(node.Arguments[i]);
      }
      node.Result = (Type)Visit(node.Result);
      if (node.FreeVariables.Count == 0 && node.TypeParameters.Count > 0)
      {
        monomorphizationVisitor.RegisterPolymorphicMapType(node);
      }
      return node;
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      node = (CtorType)node.Clone();
      for (int i = 0; i < node.Arguments.Count; ++i)
      {
        node.Arguments[i] = (Type)Visit(node.Arguments[i]);
      }

      if (node.Arguments.Any(HasFreeTypeVariables))
      {
        return node;
      }
      
      var typeCtorDecl = node.Decl;
      if (MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(typeCtorDecl))
      {
        return new CtorType(node.tok, monomorphizationVisitor.InstantiateTypeCtorDecl(typeCtorDecl, node.Arguments),
          new List<Type>());
      }

      return node;
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      return VisitType(node.ExpandedType);
    }

    public override Type VisitType(Type node)
    {
      return (Type)Visit(node);
    }
    
    public override Type VisitTypeProxy(TypeProxy node)
    {
      return VisitType(TypeProxy.FollowProxy(node));
    }

    public override Type VisitBvTypeProxy(BvTypeProxy node)
    {
      return VisitType(TypeProxy.FollowProxy(node));
    }

    public override Expr VisitExpr(Expr node)
    {
      node = base.VisitExpr(node);
      node.Type = VisitType(node.Type);
      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if (variableMapping.ContainsKey(node.Decl))
      {
        return new IdentifierExpr(node.tok, variableMapping[node.Decl], node.Immutable);
      }

      if (boundVarSubst.ContainsKey(node.Decl))
      {
        return new IdentifierExpr(node.tok, boundVarSubst[node.Decl], node.Immutable);
      }

      var identifierExpr = base.VisitIdentifierExpr(node);
      identifierExpr.Type = VisitType(identifierExpr.Type);
      return identifierExpr;
    }

    public override Expr VisitBinderExpr(BinderExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(x.tok, new TypedIdent(x.tok, x.Name, VisitType(x.TypedIdent.Type)),
          x.Attributes));
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Add(x, oldToNew[x]);
      }

      var expr = (BinderExpr)base.VisitBinderExpr(node);
      expr.Type = VisitType(expr.Type);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
      // We process triggers of quantifier expressions here, because otherwise the
      // substitutions for bound variables have to be leaked outside this procedure.
      if (node is QuantifierExpr quantifierExpr)
      {
        if (quantifierExpr.Triggers != null)
        {
          ((QuantifierExpr)expr).Triggers = VisitTrigger(quantifierExpr.Triggers);
        }
      }

      if (node.Attributes != null)
      {
        expr.Attributes = VisitQKeyValue(node.Attributes);
      }

      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }

      if (expr.TypeParameters.Count > 0)
      {
        if (expr is LambdaExpr lambdaExpr)
        {
          monomorphizationVisitor.AddBinderExprMonomorphizer(new LambdaExprMonomorphizer(lambdaExpr, monomorphizationVisitor));
        }
        else if (expr is ForallExpr forallExpr)
        {
          monomorphizationVisitor.AddBinderExprMonomorphizer(new ForallExprMonomorphizer(forallExpr, monomorphizationVisitor));
        }
        else if (expr is ExistsExpr existsExpr)
        {
          monomorphizationVisitor.AddBinderExprMonomorphizer(new ExistsExprMonomorphizer(existsExpr, monomorphizationVisitor));
        }
        else
        {
          throw new Cce.UnreachableException();
        }
      }

      return expr;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
      return (QuantifierExpr)VisitBinderExpr(node);
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      var oldToNew = node.Dummies.ToDictionary(x => x,
        x => new BoundVariable(x.tok, new TypedIdent(x.tok, x.Name, VisitType(x.TypedIdent.Type)),
          x.Attributes));
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Add(x, oldToNew[x]);
      }

      var expr = (LetExpr)base.VisitLetExpr(node);
      expr.Type = VisitType(expr.Type);
      expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();
      foreach (var x in node.Dummies)
      {
        boundVarSubst.Remove(x);
      }

      return expr;
    }

    private static bool HasFreeTypeVariables(Type type)
    {
      return new FreeTypeVariableChecker().IsPolymorphic(type);
    }

    class FreeTypeVariableChecker
    {
      private HashSet<TypeVariable> boundTypeVariables = new HashSet<TypeVariable>();
      public bool IsPolymorphic(Type type)
      {
        type = TypeProxy.FollowProxy(type).Expanded;
        if (type is BasicType or BvType or FloatType)
        {
          return false;
        }
        if (type is TypeVariable typeVariable)
        {
          return !boundTypeVariables.Contains(typeVariable);
        }
        if (type is CtorType ctorType)
        {
          return ctorType.Arguments.Any(IsPolymorphic);
        }
        if (type is MapType mapType)
        {
          mapType.TypeParameters.ForEach(x => boundTypeVariables.Add(x));
          var returnVal = mapType.Arguments.Any(IsPolymorphic) || IsPolymorphic(mapType.Result);
          mapType.TypeParameters.ForEach(x => boundTypeVariables.Remove(x));
          return returnVal;
        }
        throw new Cce.UnreachableException();
      }
    }
  }

  class MonomorphizationVisitor : VarDeclOnceStandardVisitor
  {
    /*
     * This class monomorphizes a Boogie program. Monomorphization starts from
     * a traversal of monomorphic procedures. Any polymorphic function or type
     * encountered is monomorphized based on actual type parameters. The body of
     * each encountered function is recursively traversed.
     *
     * If the program contains a polymorphic procedure, a monomorphic version of
     * the procedure is created by substituting a fresh uninterpreted type for
     * each type parameter.
     *
     * MonomorphizationVisitor uses a helper class MonomorphizationDuplicator.
     * While the former does in-place update as a result of monomorphization,
     * the latter creates a duplicate copy. MonomorphizationDuplicator is needed
     * because a polymorphic function, type, or procedure may be visited several
     * times in different type contexts.
     *
     * A polymorphic map type T is converted into a single-constructor datatype with
     * one field for each instantiation I of T encountered in the program. An operation
     * on a value of I-instantiation of T is translated to the corresponding operation
     * on the field corresponding to I in the datatype corresponding to T. Polymorphic
     * lambdas are translated to a constructed value of the datatype; the field
     * corresponding to I is initialized by instantiating the polymorphic lambda on I.
     *
     * A polymorphic forall quantifier is translated to a conjunction of monomorphic
     * instances of the quantifier obtained by instantiating the bound type parameters
     * on concrete types collected from the program. Similarly, a polymorphic exists
     * quantifier is translated to a disjunction. This instantiation scheme is "sound"
     * if each forall quantifier occurs in positive polarity and each exists quantifier
     * occurs in negative polarity in the verification condition submitted for
     * satisfiability checking.
     *
     * The implementation uses a heuristic for collecting types for monomorphizing quantifiers.
     * The body of the quantifier is examined to collect all instances of polymorphic types
     * and functions mentioned in it. Suppose an instantiation T X of the polymorphic type T
     * (with one parameter instantiated to X) is collected. If X is a type parameter of the
     * enclosing quantifier, then each concrete type used in any instantiation of T becomes a
     * candidate for instantiating the type quantifier. This scheme is easily generalized to
     * types with more than one type parameter. References to polymorphic functions are handled
     * similarly. Once candidates for all bound type parameters of the quantifier are collected,
     * instantiation is performed using the Cartesian product of the candidates for each parameter.
     *
     * A big source of complexity in the implementation is the handling of nested binders.
     * To handle nesting appropriately, the implementation
     * (1) dynamically discovers polymorphic binders that become candidates for instantiation, and
     * (2) finalizes the instantiation of a binder only when the instantiation of all of its
     * children has been finalized.
     */

    private CoreOptions Options { get; }
    
    private Program program;
    private Dictionary<string, Function> nameToFunction;
    private Dictionary<string, Procedure> nameToProcedure;
    private Dictionary<string, Implementation> nameToImplementation;
    private Dictionary<string, TypeCtorDecl> nameToTypeCtorDecl;
    private Dictionary<Function, Dictionary<List<Type>, Function>> functionInstantiations;
    private Dictionary<Procedure, Dictionary<List<Type>, Procedure>> procInstantiations;
    private Dictionary<Implementation, Dictionary<List<Type>, Implementation>> implInstantiations;
    private Dictionary<TypeCtorDecl, Dictionary<List<Type>, TypeCtorDecl>> typeInstantiations;
    private HashSet<Declaration> newInstantiatedDeclarations;
    private List<BinderExprMonomorphizer> binderExprMonomorphizers;
    private Dictionary<MapType, PolymorphicMapInfo> polymorphicMapInfos;
    private Dictionary<DeclWithFormals, Dictionary<string, Type>> declWithFormalsToTypeInstantiation;
    private Dictionary<TypeCtorDecl, List<Type>> typeCtorDeclToTypeInstantiation;
    private HashSet<TypeCtorDecl> visitedTypeCtorDecls;
    private HashSet<Function> visitedFunctions;
    private Dictionary<Procedure, Implementation> procToImpl;
    private readonly HashSet<Function> originalFunctions;
    private readonly HashSet<Constant> originalConstants;
    // Note that original axioms refer to axioms of the original program which might have been updated in-place during monomorphization.
    public readonly Dictionary<Axiom, HashSet<Axiom>> originalAxiomToSplitAxioms;
    private readonly Dictionary<Axiom, FunctionAndConstantCollector> originalAxiomToOriginalSymbols;

    private MonomorphizationVisitor(CoreOptions options, Program program, HashSet<Axiom> polymorphicFunctionAxioms)
    {
      Options = options;
      this.program = program;
      originalFunctions = program.Functions.ToHashSet();
      originalConstants = program.Constants.ToHashSet();
      originalAxiomToSplitAxioms = program.Axioms.ToDictionary(ax => ax, _ => new HashSet<Axiom>());
      originalAxiomToOriginalSymbols = program.Axioms.ToDictionary(ax => ax, ax => new FunctionAndConstantCollector(ax));
      implInstantiations = new Dictionary<Implementation, Dictionary<List<Type>, Implementation>>();
      nameToImplementation = new Dictionary<string, Implementation>();
      program.TopLevelDeclarations.OfType<Implementation>().Where(impl => impl.TypeParameters.Count > 0).ForEach(
        impl =>
        {
          nameToImplementation.Add(impl.Name, impl);
          implInstantiations.Add(impl, new Dictionary<List<Type>, Implementation>(new ListComparer<Type>()));
        });
      procInstantiations = new Dictionary<Procedure, Dictionary<List<Type>, Procedure>>();
      nameToProcedure = new Dictionary<string, Procedure>();
      program.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.TypeParameters.Count > 0).ForEach(
        proc =>
        {
          nameToProcedure.Add(proc.Name, proc);
          procInstantiations.Add(proc, new Dictionary<List<Type>, Procedure>(new ListComparer<Type>()));
        });
      functionInstantiations = new Dictionary<Function, Dictionary<List<Type>, Function>>();
      nameToFunction = new Dictionary<string, Function>();
      program.TopLevelDeclarations.OfType<Function>().Where(function => function.TypeParameters.Count > 0).ForEach(
        function =>
        {
          nameToFunction.Add(function.Name, function);
          functionInstantiations.Add(function, new Dictionary<List<Type>, Function>(new ListComparer<Type>()));
        });
      declWithFormalsToTypeInstantiation = new Dictionary<DeclWithFormals, Dictionary<string, Type>>();
      typeCtorDeclToTypeInstantiation = new Dictionary<TypeCtorDecl, List<Type>>();
      typeInstantiations = new Dictionary<TypeCtorDecl, Dictionary<List<Type>, TypeCtorDecl>>();
      newInstantiatedDeclarations = new HashSet<Declaration>();
      binderExprMonomorphizers = new List<BinderExprMonomorphizer>();
      polymorphicMapInfos = new Dictionary<MapType, PolymorphicMapInfo>();
      nameToTypeCtorDecl = new Dictionary<string, TypeCtorDecl>();
      program.TopLevelDeclarations.OfType<TypeCtorDecl>()
        .Where(typeCtorDecl => MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(typeCtorDecl)).ForEach(
          typeCtorDecl =>
          {
            nameToTypeCtorDecl.Add(typeCtorDecl.Name, typeCtorDecl);
            typeInstantiations.Add(typeCtorDecl, new Dictionary<List<Type>, TypeCtorDecl>(new ListComparer<Type>()));
          });
      visitedTypeCtorDecls = new HashSet<TypeCtorDecl>();
      visitedFunctions = new HashSet<Function>();
      procToImpl = new Dictionary<Procedure, Implementation>();
      program.TopLevelDeclarations.OfType<Implementation>().ForEach(impl => procToImpl[impl.Proc] = impl);
      program.RemoveTopLevelDeclarations(decl => 
        decl is Implementation impl && implInstantiations.ContainsKey(impl) ||
        decl is Procedure proc && procInstantiations.ContainsKey(proc) ||
        decl is Function function && functionInstantiations.ContainsKey(function) ||
        decl is TypeCtorDecl typeCtorDecl && typeInstantiations.ContainsKey(typeCtorDecl) ||
        decl is TypeSynonymDecl typeSynonymDecl && typeSynonymDecl.TypeParameters.Count > 0 ||
        decl is Axiom axiom && polymorphicFunctionAxioms.Contains(axiom));
    }
    
    public static MonomorphizationVisitor Initialize(CoreOptions options, Program program, HashSet<Axiom> polymorphicFunctionAxioms)
    {
      var monomorphizationVisitor =
        new MonomorphizationVisitor(options, program, polymorphicFunctionAxioms);
      // ctorTypes contains all the uninterpreted types created for monomorphizing top-level polymorphic implementations 
      // that must be verified. The types in ctorTypes are reused across different implementations.
      var ctorTypes = new List<Type>();
      var typeCtorDecls = new HashSet<TypeCtorDecl>();
      monomorphizationVisitor.implInstantiations.Keys.Where(impl => !impl.IsSkipVerification(options)).ForEach(impl =>
      {
        for (int i = ctorTypes.Count; i < impl.TypeParameters.Count; i++)
        {
          var typeParam = impl.TypeParameters[i];
          var typeCtorDecl = new TypeCtorDecl(typeParam.tok, $"{typeParam.Name}_{typeParam.UniqueId}", 0);
          typeCtorDecls.Add(typeCtorDecl);
          ctorTypes.Add(new CtorType(typeParam.tok, typeCtorDecl,  new List<Type>()));
        }
        var actualTypeParams = ctorTypes.GetRange(0, impl.TypeParameters.Count);
        var instantiatedImpl = monomorphizationVisitor.InstantiateImplementation(impl, actualTypeParams);
        instantiatedImpl.Proc = monomorphizationVisitor.InstantiateProcedure(impl.Proc, actualTypeParams);
      });
      monomorphizationVisitor.VisitProgram(program);
      monomorphizationVisitor.AddInstantiatedDeclarations();
      program.AddTopLevelDeclarations(typeCtorDecls);
      monomorphizationVisitor.FixpointOnBinderExprMonomorphizers();
      var polymorphicMapAndBinderSubstituter = new PolymorphicMapAndBinderSubstituter(monomorphizationVisitor);
      var polymorphicMapDatatypeCtorDecls =
        monomorphizationVisitor.polymorphicMapInfos.Values.Select(polymorphicMapInfo =>
          polymorphicMapInfo.CreateDatatypeTypeCtorDecl(polymorphicMapAndBinderSubstituter)).ToList();
      var splitAxioms = polymorphicMapAndBinderSubstituter.Substitute(program);
      UpdateDependencies(monomorphizationVisitor);
      program.RemoveTopLevelDeclarations(decl => decl is Axiom);
      program.AddTopLevelDeclarations(splitAxioms);
      program.AddTopLevelDeclarations(polymorphicMapDatatypeCtorDecls);
      Contract.Assert(MonomorphismChecker.IsMonomorphic(program));
      return monomorphizationVisitor;
    }

    /// <summary>
    /// Original program axioms were replaced with new splitAxioms. Program constants and functions that had
    /// those original axioms as dependencies need their references updated to the new axioms.
    /// Axioms / functions could both have been instantiated, which adds some complexity.
    /// </summary>
    private static void UpdateDependencies(MonomorphizationVisitor monomorphizationVisitor)
    {
      foreach (var (originalAxiom, newAxioms) in monomorphizationVisitor.originalAxiomToSplitAxioms)
      {
        var originalAxiomFc = monomorphizationVisitor.originalAxiomToOriginalSymbols[originalAxiom];
        var originalAxiomFunctions = originalAxiomFc.Functions;

        var newAxiomFunctions = new Dictionary<Axiom, HashSet<Function>>();
        var newAxiomConstants = new Dictionary<Axiom, HashSet<Constant>>();

        foreach (var newAxiom in newAxioms)
        {
          var newAxiomFc = new FunctionAndConstantCollector(newAxiom);
          newAxiomFunctions.Add(newAxiom, newAxiomFc.Functions);
          newAxiomConstants.Add(newAxiom, newAxiomFc.Constants);
        }

        // Update function dependencies.
        foreach (var function in monomorphizationVisitor.originalFunctions)
        {
          if (!function.DefinitionAxioms.Contains(originalAxiom))
          {
            continue;
          }
          if (function.DefinitionAxiom == originalAxiom)
          {
            function.DefinitionAxiom = null;
          }
          foreach (var newAxiom in newAxioms)
          {
            if (function.TypeParameters.Any()) // Polymorphic function
            {
              var functionInstantiations =
                monomorphizationVisitor.functionInstantiations[function].Values.ToHashSet();
              var instancesToAddDependency = originalAxiomFunctions.Contains(function)
                ? newAxiomFunctions[newAxiom].Intersect(functionInstantiations)
                : functionInstantiations;
              foreach (var inst in instancesToAddDependency)
              {
                inst.OtherDefinitionAxioms.Add(newAxiom);
              }
            }
            else // Non-monomorphized function
            {
              if (!originalAxiomFunctions.Contains(function) || newAxiomFunctions[newAxiom].Contains(function))
              {
                function.OtherDefinitionAxioms.Add(newAxiom);
              }
            }
          }
          function.OtherDefinitionAxioms.Remove(originalAxiom);
        }

        // Update constant dependencies.
        foreach (var constant in monomorphizationVisitor.originalConstants)
        {
          if (constant.DefinitionAxioms.Contains(originalAxiom))
          {
            foreach (var newAxiom in newAxioms.Where(ax => newAxiomConstants[ax].Contains(constant)))
            {
              constant.DefinitionAxioms.Add(newAxiom);
            }
            constant.DefinitionAxioms.Remove(originalAxiom);
          }
        }
      }
    }

    private sealed class FunctionAndConstantCollector : ReadOnlyVisitor
    {
      public HashSet<Function> Functions { get; }
      public HashSet<Constant> Constants { get; }
      
      public FunctionAndConstantCollector(Axiom axiom)
      {
        Functions = new HashSet<Function>();
        Constants = new HashSet<Constant>();
        VisitAxiom(axiom);
      }

      public override Expr VisitNAryExpr(NAryExpr node)
      {
        if (node.Fun is FunctionCall functionCall)
        {
          Functions.Add(functionCall.Func);
        }
        return base.VisitNAryExpr(node);
      }

      public override Expr VisitIdentifierExpr(IdentifierExpr node)
      {
        if (node.Decl is Constant c)
        {
          Constants.Add(c);
        }
        return base.VisitIdentifierExpr(node);
      }
    }

    /*
     * Binder expressions may be nested inside other binder expressions. The instantiation of known binder
     * expressions using known type and function instantiations may discover more binder expressions and
     * create more type and function instantiation. After the program has been visited, the top-level binder
     * expressions have been discovered. The following method is called subsequently to execute a fixpoint
     * on the set of binder expressions, function instantiations, and type instantiations.
     */
    private void FixpointOnBinderExprMonomorphizers()
    {
      var moreWorkNeeded = true;
      while (moreWorkNeeded)
      {
        moreWorkNeeded = false;

        // binderExprMonomorphizers is modified inside the loop so iterate over a copy of it
        var oldBinderExprMonomorphizers = new List<BinderExprMonomorphizer>(binderExprMonomorphizers);
        foreach (var binderExprMonomorphizer in oldBinderExprMonomorphizers)
        {
          if (binderExprMonomorphizer.Instantiate())
          {
            // more instances created in binderExprMonomorphizer
            moreWorkNeeded = true;
          }
        }

        if (newInstantiatedDeclarations.Count > 0)
        {
          // more function/type instantiations were created 
          AddInstantiatedDeclarations();
          moreWorkNeeded = true;
        }

        if (oldBinderExprMonomorphizers.Count < binderExprMonomorphizers.Count)
        {
          // the instantiation in some binderExprMonomorphizer resulted in the discovery of a binder expression
          moreWorkNeeded = true;
        }
      }
    }

    public Dictionary<BinderExpr, BinderExprMonomorphizer> GetBinderExprMonomorphizers()
    {
      return binderExprMonomorphizers.ToDictionary(x => x.BinderExpr, x => x);
    }

    public IEnumerable<List<Type>> AbsyInstantiations(Absy decl)
    {
      if (decl is Function function)
      {
        return functionInstantiations[function].Keys;
      }
      if (decl is TypeCtorDecl typeCtorDecl)
      {
        return typeInstantiations[typeCtorDecl].Keys;
      }
      if (decl is MapType mapType)
      {
        return polymorphicMapInfos[mapType].Instances;
      }
      throw new Cce.UnreachableException();
    }

    public PolymorphicMapInfo RegisterPolymorphicMapType(Type type)
    {
      var mapType = (MapType)LookupType(type);
      if (!polymorphicMapInfos.ContainsKey(mapType))
      {
        polymorphicMapInfos[mapType] = new PolymorphicMapInfo(this, mapType);
      }
      return polymorphicMapInfos[mapType];
    }

    public void AddBinderExprMonomorphizer(BinderExprMonomorphizer binderExprMonomorphizer)
    {
      binderExprMonomorphizers.Add(binderExprMonomorphizer);
    }

    public void InlineCallCmd(CallCmd callCmd, List<Type> actualTypeParams)
    {
      if (procToImpl.ContainsKey(callCmd.Proc))
      {
        var impl = procToImpl[callCmd.Proc];
        if (IsInlined(impl))
        {
          InstantiateImplementation(impl, actualTypeParams);
        }
      }  
    }
    
    private bool IsInlined(Implementation impl)
    {
      if (Options.ProcedureInlining == CoreOptions.Inlining.None)
      {
        return false;
      }
      Expr inlineAttr = impl.FindExprAttribute("inline");
      if (inlineAttr == null)
      {
        inlineAttr = impl.Proc.FindExprAttribute("inline");
      }
      return inlineAttr != null;
    }

    private Axiom InstantiateAxiom(Axiom axiom, List<Type> actualTypeParams)
    {
      var axiomExpr = InstantiateBinderExpr((BinderExpr)axiom.Expr, actualTypeParams);
      var instantiatedAxiom = new Axiom(axiom.tok, axiomExpr, axiom.Comment, axiom.Attributes);
      if (originalAxiomToSplitAxioms.ContainsKey(axiom)) {
        originalAxiomToSplitAxioms[axiom].Add(instantiatedAxiom);
      }
      newInstantiatedDeclarations.Add(instantiatedAxiom);
      return instantiatedAxiom;
    }

    public Expr InstantiateBinderExpr(BinderExpr binderExpr, List<Type> actualTypeParams)
    {
      var binderExprTypeParameters = binderExpr.TypeParameters;
      binderExpr.TypeParameters = new List<TypeVariable>();
      var newBinderExpr = (BinderExpr)InstantiateAbsy(binderExpr, binderExprTypeParameters.MapTo(actualTypeParams),
        new Dictionary<Variable, Variable>());
      binderExpr.TypeParameters = binderExprTypeParameters;
      if (newBinderExpr is QuantifierExpr quantifierExpr && quantifierExpr.Dummies.Count == 0)
      {
        return quantifierExpr.Body;
      }
      if (binderExpr is LambdaExpr)
      {
        var polymorphicMapInfo = RegisterPolymorphicMapType(newBinderExpr.Type);
        newBinderExpr.Type = polymorphicMapInfo.GetFieldType(actualTypeParams);
      }
      return newBinderExpr;
    }
      
    public Function InstantiateFunction(Function func, List<Type> actualTypeParams)
    {
      if (!functionInstantiations[func].ContainsKey(actualTypeParams))
      {
        var funcTypeParamInstantiation = func.TypeParameters.MapTo(actualTypeParams);
        var instantiatedFunction =
          InstantiateFunctionSignature(func, actualTypeParams, funcTypeParamInstantiation);
        var variableMapping = func.InParams.MapTo(instantiatedFunction.InParams);
        newInstantiatedDeclarations.Add(instantiatedFunction);
        functionInstantiations[func][actualTypeParams] = instantiatedFunction;
        declWithFormalsToTypeInstantiation[instantiatedFunction] =
          func.TypeParameters.Select(x => x.Name).MapTo(actualTypeParams);
        if (func.Body != null)
        {
          instantiatedFunction.Body = (Expr) InstantiateAbsy(func.Body, funcTypeParamInstantiation, variableMapping);
        }
        else if (func.DefinitionBody != null)
        {
          instantiatedFunction.DefinitionBody =
            (NAryExpr) InstantiateAbsy(func.DefinitionBody, funcTypeParamInstantiation, variableMapping);
        }
        else if (func.DefinitionAxiom != null)
        {
          instantiatedFunction.DefinitionAxiom =
            InstantiateAxiom(func.DefinitionAxiom, actualTypeParams);
        }
      }
      return functionInstantiations[func][actualTypeParams];
    }

    private void AddInstantiatedDeclarations()
    {
      program.AddTopLevelDeclarations(newInstantiatedDeclarations);
      newInstantiatedDeclarations = new HashSet<Declaration>();
    }

    private Absy InstantiateAbsy(Absy absy, Dictionary<TypeVariable, Type> typeParamInstantiation,
      Dictionary<Variable, Variable> variableMapping)
    {
      var monomorphizationDuplicator =
        new MonomorphizationDuplicator(this, typeParamInstantiation, variableMapping);
      return monomorphizationDuplicator.Visit(absy);
    }  

    public Procedure InstantiateProcedure(Procedure proc, List<Type> actualTypeParams)
    {
      if (!procInstantiations[proc].ContainsKey(actualTypeParams))
      {
        var procTypeParamInstantiation = proc.TypeParameters.MapTo(actualTypeParams);
        var instantiatedInParams = InstantiateFormals(proc.InParams, procTypeParamInstantiation);
        var instantiatedOutParams = InstantiateFormals(proc.OutParams, procTypeParamInstantiation);
        var variableMapping = proc.InParams.Union(proc.OutParams).MapTo(instantiatedInParams.Union(instantiatedOutParams));
        var requires = proc.Requires.Select(requires => new Requires(requires.tok, requires.Free,
          (Expr) InstantiateAbsy(requires.Condition, procTypeParamInstantiation, variableMapping), requires.Comment)).ToList();
        var modifies = proc.Modifies.Select(ie =>
          (IdentifierExpr) InstantiateAbsy(ie, procTypeParamInstantiation, variableMapping)).ToList();
        var ensures = proc.Ensures.Select(ensures => new Ensures(ensures.tok, ensures.Free,
          (Expr) InstantiateAbsy(ensures.Condition, procTypeParamInstantiation, variableMapping), ensures.Comment)).ToList();
        var instantiatedProc = new Procedure(proc.tok, MkInstanceName(proc.Name, actualTypeParams),
          new List<TypeVariable>(), instantiatedInParams, instantiatedOutParams, proc.IsPure, requires, modifies, ensures,
          proc.Attributes == null ? null : VisitQKeyValue(proc.Attributes));
        instantiatedProc.OriginalDeclWithFormals = proc;
        newInstantiatedDeclarations.Add(instantiatedProc);
        procInstantiations[proc][actualTypeParams] = instantiatedProc;
        declWithFormalsToTypeInstantiation[instantiatedProc] =
          proc.TypeParameters.Select(x => x.Name).MapTo(actualTypeParams);
      }
      return procInstantiations[proc][actualTypeParams];
    }

    public Implementation InstantiateImplementation(Implementation impl, List<Type> actualTypeParams)
    {
      if (!implInstantiations[impl].ContainsKey(actualTypeParams))
      {
        var implTypeParamInstantiation = impl.TypeParameters.MapTo(actualTypeParams);
        var instantiatedInParams = InstantiateFormals(impl.InParams, implTypeParamInstantiation);
        var instantiatedOutParams = InstantiateFormals(impl.OutParams, implTypeParamInstantiation);
        var instantiatedLocalVariables = InstantiateLocalVariables(impl.LocVars, implTypeParamInstantiation);
        var variableMapping = impl.InParams.Union(impl.OutParams).Union(impl.LocVars).MapTo(instantiatedInParams.Union(instantiatedOutParams).Union(instantiatedLocalVariables));
        var blocks = impl.Blocks
          .Select(block => (Block)InstantiateAbsy(block, implTypeParamInstantiation, variableMapping)).ToList();
        var blockMapping = impl.Blocks.MapTo(blocks);
        blocks.ForEach(block =>
        {
          if (block.TransferCmd is GotoCmd gotoCmd)
          {
            gotoCmd.labelTargets = gotoCmd.labelTargets.Select(target => blockMapping[target]).ToList();
            gotoCmd.labelNames = new List<string>(gotoCmd.labelNames);
          }
        });
        var instantiatedImpl = new Implementation(impl.tok, MkInstanceName(impl.Name, actualTypeParams),
          new List<TypeVariable>(), instantiatedInParams, instantiatedOutParams, instantiatedLocalVariables, blocks,
          impl.Attributes == null ? null : VisitQKeyValue(impl.Attributes));
        instantiatedImpl.OriginalDeclWithFormals = impl;
        instantiatedImpl.Proc = InstantiateProcedure(impl.Proc, actualTypeParams);
        newInstantiatedDeclarations.Add(instantiatedImpl);
        implInstantiations[impl][actualTypeParams] = instantiatedImpl;
        declWithFormalsToTypeInstantiation[instantiatedImpl] =
          impl.TypeParameters.Select(x => x.Name).MapTo(actualTypeParams);
      }
      return implInstantiations[impl][actualTypeParams];
    }

    private List<Variable> InstantiateFormals(List<Variable> variables,
      Dictionary<TypeVariable, Type> declTypeParamInstantiation)
    {
      var monomorphizationDuplicator = new MonomorphizationDuplicator(this, declTypeParamInstantiation);
      var instantiatedVariables =
        variables.Select(x => (Formal)x).Select(x =>
            new Formal(x.tok,
              new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name,
                monomorphizationDuplicator.VisitType(x.TypedIdent.Type)),
              x.InComing, x.Attributes == null ? null : monomorphizationDuplicator.VisitQKeyValue(x.Attributes)))
          .ToList<Variable>();
      return instantiatedVariables;
    }

    private List<Variable> InstantiateLocalVariables(List<Variable> variables,
      Dictionary<TypeVariable, Type> declTypeParamInstantiation)
    {
      var monomorphizationDuplicator = new MonomorphizationDuplicator(this, declTypeParamInstantiation);
      var instantiatedVariables =
        variables.Select(x =>
            new LocalVariable(x.tok,
              new TypedIdent(x.TypedIdent.tok, x.TypedIdent.Name,
                monomorphizationDuplicator.VisitType(x.TypedIdent.Type))))
          .ToList<Variable>();
      return instantiatedVariables;
    }

    private Function InstantiateFunctionSignature(Function func, List<Type> actualTypeParams,
      Dictionary<TypeVariable, Type> funcTypeParamInstantiation)
    {
      var instantiatedInParams = InstantiateFormals(func.InParams, funcTypeParamInstantiation);
      var instantiatedOutParams = InstantiateFormals(func.OutParams, funcTypeParamInstantiation);
      var instantiatedFunction = new Function(
        func.tok,
        MkInstanceName(func.Name, actualTypeParams),
        new List<TypeVariable>(),
        instantiatedInParams,
        instantiatedOutParams.First(),
        func.Comment,
        func.Attributes);
      instantiatedFunction.OriginalDeclWithFormals = func;
      return instantiatedFunction;
    }

    public TypeCtorDecl InstantiateTypeCtorDecl(TypeCtorDecl typeCtorDecl, List<Type> actualTypeParams)
    {
      if (!typeInstantiations[typeCtorDecl].ContainsKey(actualTypeParams))
      {
        if (typeCtorDecl is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
        {
          var newDatatypeTypeCtorDecl = new DatatypeTypeCtorDecl(
            new TypeCtorDecl(datatypeTypeCtorDecl.tok,
              MkInstanceName(datatypeTypeCtorDecl.Name, actualTypeParams), 0,
              datatypeTypeCtorDecl.Attributes));
          newDatatypeTypeCtorDecl.OriginalTypeCtorDecl = datatypeTypeCtorDecl;
          newInstantiatedDeclarations.Add(newDatatypeTypeCtorDecl);
          typeInstantiations[datatypeTypeCtorDecl]
            .Add(actualTypeParams, newDatatypeTypeCtorDecl);
          typeCtorDeclToTypeInstantiation[newDatatypeTypeCtorDecl] = actualTypeParams;
          datatypeTypeCtorDecl.Constructors.ForEach(constructor =>
          {
            var function = InstantiateFunctionSignature(constructor, actualTypeParams,
              constructor.TypeParameters.MapTo(actualTypeParams));
            newDatatypeTypeCtorDecl.AddConstructor(new DatatypeConstructor(function));
          });
        }
        else
        {
          var newTypeCtorDecl =
            new TypeCtorDecl(typeCtorDecl.tok, MkInstanceName(typeCtorDecl.Name, actualTypeParams), 0,
              typeCtorDecl.Attributes);
          newTypeCtorDecl.OriginalTypeCtorDecl = typeCtorDecl;
          newInstantiatedDeclarations.Add(newTypeCtorDecl);
          typeInstantiations[typeCtorDecl].Add(actualTypeParams, newTypeCtorDecl);
          typeCtorDeclToTypeInstantiation[newTypeCtorDecl] = actualTypeParams;
        }
      }

      return typeInstantiations[typeCtorDecl][actualTypeParams];
    }

    public static string MkInstanceName(string name, List<Type> actualTypeParams)
    {
      actualTypeParams.ForEach(x => name = $"{name}_{x.UniqueId}");
      return name;
    }

    public Type LookupType(Type type)
    {
      type = TypeProxy.FollowProxy(type.Expanded);
      if (type is MapType mapType && mapType.FreeVariables.Count == 0)
      {
        var instantiatedTypeArguments = mapType.Arguments.Select(x => LookupType(x)).ToList();
        var instantiatedTypeResult = LookupType(mapType.Result);
        return new MapType(mapType.tok, new List<TypeVariable>(mapType.TypeParameters), instantiatedTypeArguments,
          instantiatedTypeResult);
      }
      if (type is CtorType ctorType && ctorType.FreeVariables.Count == 0 &&
          MonomorphismChecker.DoesTypeCtorDeclNeedMonomorphization(ctorType.Decl))
      {
        var instantiatedTypeArguments = ctorType.Arguments.Select(x => LookupType(x)).ToList();
        return new CtorType(ctorType.tok, typeInstantiations[ctorType.Decl][instantiatedTypeArguments],
          new List<Type>());
      }
      return type;
    }

    public IsConstructor InstantiateIsConstructor(IsConstructor isConstructor, List<Type> actualTypeParams)
    {
      InstantiateTypeCtorDecl(isConstructor.DatatypeTypeCtorDecl, actualTypeParams);
      var instantiatedDatatypeTypeCtorDecl =
        (DatatypeTypeCtorDecl)typeInstantiations[isConstructor.DatatypeTypeCtorDecl][
          actualTypeParams];
      return new IsConstructor(isConstructor.tok, instantiatedDatatypeTypeCtorDecl, isConstructor.ConstructorIndex);
    }

    public FieldAccess InstantiateFieldAccess(FieldAccess fieldAccess, List<Type> actualTypeParams)
    {
      InstantiateTypeCtorDecl(fieldAccess.DatatypeTypeCtorDecl, actualTypeParams);
      var instantiatedDatatypeTypeCtorDecl =
        (DatatypeTypeCtorDecl)typeInstantiations[fieldAccess.DatatypeTypeCtorDecl][
          actualTypeParams];
      return new FieldAccess(fieldAccess.tok, fieldAccess.FieldName, instantiatedDatatypeTypeCtorDecl,
        fieldAccess.Accessors);
    }

    public FieldUpdate InstantiateFieldUpdate(FieldUpdate fieldUpdate, List<Type> actualTypeParams)
    {
      return new FieldUpdate(InstantiateFieldAccess(fieldUpdate.FieldAccess, actualTypeParams));
    }

    public TypeCtorDecl InstantiateTypeCtorDecl(string typeName, List<Type> actualTypeParams)
    {
      if (!GetType(typeName, out TypeCtorDecl typeCtorDecl))
      {
        return null;
      }
      var instantiatedFunction = InstantiateTypeCtorDecl(typeCtorDecl, actualTypeParams);
      AddInstantiatedDeclarations();
      return instantiatedFunction;
    }
    
    public Function InstantiateFunction(string functionName, Dictionary<string, Type> typeParamInstantiationMap)
    {
      if (!GetFunction(functionName, out Function function))
      {
        return null;
      }
      var actualTypeParams = function.TypeParameters.Select(tp => typeParamInstantiationMap[tp.Name]).ToList();
      var instantiatedFunction = InstantiateFunction(function, actualTypeParams);
      AddInstantiatedDeclarations();
      return instantiatedFunction;
    }

    public bool GetFunction(string functionName, out Function function)
    {
      return nameToFunction.TryGetValue(functionName, out function);
    }

    public bool GetType(string typeName, out TypeCtorDecl typeCtorDecl)
    {
      return nameToTypeCtorDecl.TryGetValue(typeName, out typeCtorDecl);
    }
    
    public bool GetTypeInstantiation(DeclWithFormals decl, out Dictionary<string, Type> value)
    {
      return declWithFormalsToTypeInstantiation.TryGetValue(decl, out value);
    }

    public bool GetTypeInstantiation(TypeCtorDecl decl, out List<Type> value)
    {
      return typeCtorDeclToTypeInstantiation.TryGetValue(decl, out value);
    }

    public override Cmd VisitCallCmd(CallCmd node)
    {
      if (node.Proc.TypeParameters.Count == 0)
      {
        return base.VisitCallCmd(node);
      }

      return new MonomorphizationDuplicator(this).VisitCallCmd(node);
    }

    public override CtorType VisitCtorType(CtorType node)
    {
      return (CtorType) new MonomorphizationDuplicator(this).VisitType(node);
    }

    public override Type VisitTypeSynonymAnnotation(TypeSynonymAnnotation node)
    {
      base.VisitTypeSynonymAnnotation(node);
      return node.ExpandedType;
    }

    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node)
    {
      node.Body = new MonomorphizationDuplicator(this).VisitType(node.Body);
      return node;
    }

    public override Expr VisitExpr(Expr node)
    {
      return new MonomorphizationDuplicator(this).VisitExpr(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      return new MonomorphizationDuplicator(this).VisitExpr(node);
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      return new MonomorphizationDuplicator(this).VisitExpr(node);
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
      return new MonomorphizationDuplicator(this).VisitFieldAssignLhs(node);
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      return new MonomorphizationDuplicator(this).VisitMapAssignLhs(node);
    }

    // this function may be called directly by monomorphizationDuplicator
    // if a non-polymorphic call to a datatype constructor/selector/membership
    // is discovered in an expression
    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node)
    {
      if (visitedTypeCtorDecls.Contains(node))
      {
        return node;
      }
      visitedTypeCtorDecls.Add(node);
      if (node is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        datatypeTypeCtorDecl.Constructors.ForEach(constructor => base.VisitFunction(constructor));
      }
      return base.VisitTypeCtorDecl(node);
    }

    // this function may be called directly by monomorphizationDuplicator
    // if a non-polymorphic function call is discovered in an expression
    public override Function VisitFunction(Function node)
    {
      if (visitedFunctions.Contains(node))
      {
        return node;
      }
      visitedFunctions.Add(node);
      return base.VisitFunction(node);
    }

    public override Constant VisitConstant(Constant node)
    {
      node = (Constant)base.VisitVariable(node);
      node.TypedIdent = new TypedIdent(node.TypedIdent.tok, node.TypedIdent.Name,
        new MonomorphizationDuplicator(this).VisitType(node.TypedIdent.Type), node.TypedIdent.WhereExpr);
      return node;
    }
  }
  
  public class Monomorphizer
  {
    /*
     * This class exposes monomorphization to the rest of Boogie. After type checking a Boogie program,
     * the static factory method Monomorphize is invoked with a Program object as a parameter. This factory
     * method does the following:
     * (1) returns if the input program is not monomorphizable,
     * (2) otherwise, creates a Monomorphizer object and monomorphizes the program,
     * (3) stashes the created Monomorphizer object inside the provided Program object.
     */

    public static MonomorphizableStatus Monomorphize(CoreOptions options, Program program)
    {
      var monomorphizableStatus = MonomorphizableChecker.IsMonomorphizable(program, out var polymorphicFunctionAxioms);
      if (monomorphizableStatus == MonomorphizableStatus.Monomorphizable)
      {
        var monomorphizationVisitor = MonomorphizationVisitor.Initialize(options, program, polymorphicFunctionAxioms);
        program.monomorphizer = new Monomorphizer(monomorphizationVisitor);
      }
      return monomorphizableStatus;
    }

    public Function InstantiateFunction(string functionName, Dictionary<string, Type> typeParamInstantiationMap)
    {
      return monomorphizationVisitor.InstantiateFunction(functionName, typeParamInstantiationMap);
    }

    public TypeCtorDecl InstantiateTypeCtorDecl(string typeCtorDeclName, List<Type> actualTypeParams)
    {
      return monomorphizationVisitor.InstantiateTypeCtorDecl(typeCtorDeclName, actualTypeParams);
    }

    public static DeclWithFormals GetOriginalDecl(DeclWithFormals decl)
    {
      return decl.OriginalDeclWithFormals ?? decl;
    }
    
    public Dictionary<string, Type> GetTypeInstantiation(DeclWithFormals decl)
    {
      if (!monomorphizationVisitor.GetTypeInstantiation(decl, out Dictionary<string, Type> value))
      {
        return null;
      }
      return value;
    }
    
    public static TypeCtorDecl GetOriginalDecl(TypeCtorDecl decl)
    {
      return decl.OriginalTypeCtorDecl ?? decl;
    }
    
    public List<Type> GetTypeInstantiation(TypeCtorDecl decl)
    {
      if (!monomorphizationVisitor.GetTypeInstantiation(decl, out List<Type> value))
      {
        return null;
      }
      return value;
    }

    private MonomorphizationVisitor monomorphizationVisitor;
    private Monomorphizer(MonomorphizationVisitor monomorphizationVisitor)
    {
      this.monomorphizationVisitor = monomorphizationVisitor;
    }
  }
}