using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie.VCExprAST
{
  public class QuantifierInstantiationEngine
  {
    /*
     * The algorithm implemented by QuantifierInstantiationEngine is a fixpoint. There are three phases.
     *
     * Start:
     *   - find instantiation sources in commands
     *   - skolemize quantifiers in the verification condition
     * At this point, a collection of quantifiers to be instantiated and a collection of instances
     * are installed.
     *
     * Execute: Repeatedly, instantiate quantifiers based on existing instances, skolemize and install new quantifiers
     * that are discovered, and install new instances discovered.
     *
     * Finish:
     *   - Rewrite quantifiers based on the discovered instances. Forall quantifiers are rewritten as a conjunction of
     *     the original quantifier and the instances. Exists quantifiers are rewritten as a disjunction of the original
     *     quantifier and the instances.
     *   - Add instances of the axioms for lambdas as assume statements in the starting block of impl.
     */

    private class QuantifierInstantiationInfo
    {
      public HashSet<string> relevantLabels;
      public Dictionary<List<VCExpr>, VCExpr> instances;

      public QuantifierInstantiationInfo(Dictionary<VCExprVar, HashSet<string>> boundVariableToLabels)
      {
        this.relevantLabels = boundVariableToLabels.Values.SelectMany(x => x).ToHashSet();
        this.instances = new Dictionary<List<VCExpr>, VCExpr>(new ListComparer<VCExpr>());
      }
    }
    
    private Dictionary<VCExprVar, VCExprQuantifier> quantifierBinding;
    private Dictionary<Function, VCExprQuantifier> lambdaDefinition;
    private Dictionary<VCExprQuantifier, QuantifierInstantiationInfo> quantifierInstantiationInfo;
    private HashSet<VCExprVar> skolemConstants;
    private Dictionary<string, HashSet<VCExpr>> labelToInstances;
    private Dictionary<string, HashSet<VCExpr>> accLabelToInstances;
    private Dictionary<Function, HashSet<List<VCExpr>>> lambdaToInstances;
    private Dictionary<Function, HashSet<List<VCExpr>>> accLambdaToInstances;
    private string quantifierBindingNamePrefix;
    private string skolemConstantNamePrefix;
    internal VCExpressionGenerator vcExprGen;
    private Boogie2VCExprTranslator exprTranslator;
    internal static ConcurrentDictionary<string, HashSet<Type>> labelToTypes = new(); // pool name may map to multiple types

    public static VCExpr Instantiate(Implementation impl, VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator exprTranslator, VCExpr vcExpr)
    {
      if (!InstantiationSourceChecker.HasInstantiationSources(impl))
      {
        return vcExpr;
      }
      var qiEngine = new QuantifierInstantiationEngine(vcExprGen, exprTranslator);
      return qiEngine.Execute(impl, vcExpr);
    }

    private QuantifierInstantiationEngine(VCExpressionGenerator vcExprGen, Boogie2VCExprTranslator exprTranslator)
    {
      this.quantifierBinding = new Dictionary<VCExprVar, VCExprQuantifier>();
      this.lambdaDefinition = new Dictionary<Function, VCExprQuantifier>();
      this.quantifierInstantiationInfo = new Dictionary<VCExprQuantifier, QuantifierInstantiationInfo>();
      this.skolemConstants = new HashSet<VCExprVar>();
      this.labelToInstances = new Dictionary<string, HashSet<VCExpr>>();
      this.accLabelToInstances = new Dictionary<string, HashSet<VCExpr>>();
      this.lambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      this.accLambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      this.quantifierBindingNamePrefix = "quantifierBinding";
      this.skolemConstantNamePrefix = "skolemConstant";
      this.vcExprGen = vcExprGen;
      this.exprTranslator = exprTranslator;
    }

    public static void SubstituteIncarnationInInstantiationSources(Cmd cmd, Substitution incarnationSubst)
    {
      var attrCmd = cmd as ICarriesAttributes;
      if (attrCmd == null)
      {
        return;
      }
      attrCmd.Attributes = CivlAttributes.ApplySubstitutionToPoolHints(incarnationSubst, attrCmd.Attributes);
    }

    public VCExpr BindQuantifier(VCExprQuantifier node)
    {
      if (node.TypeParameters.Count > 0)
      {
        return node;
      }
      var boundVariableToLabels = node.Info.instantiationLabels;
      if (boundVariableToLabels.Count < node.BoundVars.Count ||
          boundVariableToLabels.Any(kv => kv.Value.Count == 0))
      {
        return node;
      }
      var v = new VCExprVar($"{quantifierBindingNamePrefix}{quantifierBinding.Count}", Type.Bool);
      quantifierBinding[v] = node;
      quantifierInstantiationInfo[node] = new QuantifierInstantiationInfo(boundVariableToLabels);
      return v;
    }

    public void AddTerm(string label, VCExpr term)
    {
      if (!labelToInstances.ContainsKey(label))
      {
        labelToInstances[label] = new HashSet<VCExpr>();
      }
      labelToInstances[label].Add(term);
    }

    public bool IsQuantifierBinding(VCExprVar vcExprVar)
    {
      return this.quantifierBinding.ContainsKey(vcExprVar);
    }

    public VCExprVar FreshSkolemConstant(VCExprVar variable)
    {
      var skolemConstant = new VCExprVar($"{skolemConstantNamePrefix}{skolemConstants.Count}", variable.Type);
      skolemConstants.Add(skolemConstant);
      return skolemConstant;
    }

    public bool BindLambdaFunction(Function lambdaFunction)
    {
      if (lambdaDefinition.ContainsKey(lambdaFunction))
      {
        return true;
      }
      var lambdaDefinitionExpr = lambdaFunction.DefinitionAxiom.Expr as QuantifierExpr;
      if (lambdaDefinitionExpr.TypeParameters.Count > 0)
      {
        return false;
      }
      var translatedExpr = exprTranslator.Translate(lambdaDefinitionExpr) as VCExprQuantifier;
      var boundVariableToLabels = translatedExpr.Info.instantiationLabels;
      var numParametersInLambdaDefinition = lambdaDefinitionExpr.Dummies.Count - lambdaFunction.InParams.Count;
      if (boundVariableToLabels.Count < numParametersInLambdaDefinition ||
          Enumerable.Range(lambdaFunction.InParams.Count, numParametersInLambdaDefinition)
            .Any(i => boundVariableToLabels[translatedExpr.BoundVars[i]].Count == 0))
      {
        return false;
      }
      lambdaDefinition[lambdaFunction] = translatedExpr;
      quantifierInstantiationInfo[translatedExpr] = new QuantifierInstantiationInfo(boundVariableToLabels);
      lambdaToInstances[lambdaFunction] = new HashSet<List<VCExpr>>(new ListComparer<VCExpr>());
      return true;
    }

    public void AddLambdaInstances(Dictionary<Function, HashSet<List<VCExpr>>> lambdaFunctionToInstances)
    {
      AddDictionary(lambdaFunctionToInstances, this.lambdaToInstances);
    }

    public static HashSet<string> FindInstantiationHints(Variable v)
    {
      var labels = new HashSet<string>();
      var iter = v.Attributes;
      while (iter != null)
      {
        if (iter.Key == "pool")
        {
          var tok = iter.tok;
          iter.Params.ForEach(x =>
          {
            if (x is string poolName)
            {
              labels.Add(poolName);
              if (!labelToTypes.ContainsKey(poolName))
              {
                labelToTypes[poolName] = new();
              }
              labelToTypes[poolName].Add(v.TypedIdent.Type);
            }
            else
            {
              Console.WriteLine($"{tok.filename}({tok.line},{tok.col}): expected pool name");
            }
          });
        }
        iter = iter.Next;
      }
      return labels;
    }
    
    public static Dictionary<string, HashSet<VCExpr>> FindInstantiationSources(ICarriesAttributes o, Boogie2VCExprTranslator exprTranslator)
    {
      var freshInstances = new Dictionary<string, HashSet<VCExpr>>();
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "add_to_pool" && iter.Params.Count > 1)
        {
          var label = iter.Params[0] as string;
          if (label != null)
          {
            for (int i = 1; i < iter.Params.Count; i++)
            {
              var instance = iter.Params[i] as Expr;
              if (instance != null)
              {
                if (!freshInstances.ContainsKey(label))
                {
                  freshInstances[label] = new HashSet<VCExpr>();
                }
                freshInstances[label].Add(exprTranslator.Translate(instance));
              }
            }
          }
        }
        iter = iter.Next;
      }
      return freshInstances;
    }
    
    private static void AddDictionary<T, U>(Dictionary<T, HashSet<U>> @from, Dictionary<T, HashSet<U>> to)
    {
      @from.ForEach(kv =>
      {
        if (!to.ContainsKey(kv.Key))
        {
          to[kv.Key] = new HashSet<U>();
        }
        to[kv.Key].UnionWith(@from[kv.Key]);
      });
    }
    
    private static void AddDictionary<T, U>(Dictionary<T, HashSet<List<U>>> @from, Dictionary<T, HashSet<List<U>>> to)
    {
      @from.ForEach(kv =>
      {
        if (!to.ContainsKey(kv.Key))
        {
          to[kv.Key] = new HashSet<List<U>>(new ListComparer<U>());
        }
        to[kv.Key].UnionWith(@from[kv.Key]);
      });
    }
    
    private VCExpr Execute(Implementation impl, VCExpr vcExpr)
    {
      impl.Blocks.ForEach(block => block.Cmds.OfType<PredicateCmd>().ForEach(predicateCmd =>
      {
        AddDictionary(FindInstantiationSources(predicateCmd, exprTranslator), labelToInstances);
      }));
      vcExpr = Skolemizer.Skolemize(this, Polarity.Negative, vcExpr);
      while (labelToInstances.Count > 0 || lambdaToInstances.Count > 0)
      {
        /*
         * Each iteration of this loop
         * (1) moves the contents of labelToInstances into accLabelToInstances
         * (2) moves the contents of lambdaToInstances into accLambdaToInstances
         * (3) instantiates quantifiers in quantifierBinding against accLabelToInstances
         * (4) instantiates lambdas in lambdaDefinition against accLabelToInstances and accLambdaToInstances
         * Steps (3) and (4) could add more entries to quantifierBinding and lambdaDefinition.
         * These entries are handled in the same iteration of this top-level loop.
         * Steps (3) and (4) could also re-populate labelToInstances and lambdaToInstances;
         * these new entries are handled in the next iteration of this top-level loop.
         */
        AddDictionary(labelToInstances, accLabelToInstances);
        labelToInstances = new Dictionary<string, HashSet<VCExpr>>();

        AddDictionary(lambdaToInstances, accLambdaToInstances);
        lambdaToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();

        var visitedQuantifierBindings = new HashSet<VCExprVar>();
        while (visitedQuantifierBindings.Count < quantifierBinding.Count)
        {
          /*
           * quantifierBinding may be modified in each iteration of the following loop.
           * Therefore, take a snapshot of quantifierBinding.Keys to start the loop.
           */
          foreach (var v in quantifierBinding.Keys)
          {
            if (visitedQuantifierBindings.Contains(v))
            {
              continue;
            }
            visitedQuantifierBindings.Add(v);
            var quantifierExpr = quantifierBinding[v];
            var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
            if (quantifierInfo.relevantLabels.Overlaps(accLabelToInstances.Keys))
            {
              InstantiateQuantifier(quantifierExpr);
            }
          }
        }

        var visitedLambdaFunctions = new HashSet<Function>();
        while (visitedLambdaFunctions.Count < lambdaDefinition.Count)
        {
          /*
           * lambdaDefinition may be modified in each iteration of the following loop.
           * Therefore, take a snapshot of lambdaDefinition.Keys to start the loop.
           */
          foreach (var lambdaFunction in lambdaDefinition.Keys.ToList())
          {
            if (visitedLambdaFunctions.Contains(lambdaFunction))
            {
              continue;
            }
            visitedLambdaFunctions.Add(lambdaFunction);
            var quantifierExpr = lambdaDefinition[lambdaFunction];
            var quantifierInfo = quantifierInstantiationInfo[quantifierExpr];
            if (quantifierInfo.relevantLabels.Overlaps(accLabelToInstances.Keys) ||
                (accLambdaToInstances.ContainsKey(lambdaFunction) && accLambdaToInstances[lambdaFunction].Count > 0))
            {
              InstantiateLambdaDefinition(lambdaFunction);
            }
          }
        }
      }

      var lambdaAxioms = vcExprGen.NAry(VCExpressionGenerator.AndOp, lambdaDefinition.Values
        .SelectMany(quantifierExpr =>
          quantifierInstantiationInfo[quantifierExpr].instances.Values.ToList()).ToList());
      return vcExprGen.Implies(lambdaAxioms, LetConvert(vcExpr));
    }
    
    private VCExpr LetConvert(VCExpr vcExpr)
    {
      var bindings = BindingCollector.CollectBindings(this, vcExpr).ToList();
      if (bindings.Count == 0)
      {
        return vcExpr;
      }
      var rhss = new List<VCExprLetBinding>();
      foreach (var binding in bindings)
      {
        rhss.Add(new VCExprLetBinding(binding, LetConvert(this.AugmentWithInstances(quantifierBinding[binding]))));
      }
      return vcExprGen.Let(rhss, vcExpr);
    }

    private VCExpr AugmentWithInstances(VCExprQuantifier quantifierExpr)
    {
      var instances = quantifierInstantiationInfo[quantifierExpr].instances;
      if (quantifierExpr.Quan == Quantifier.ALL)
      {
        var instantiatedConjuncts = vcExprGen.NAry(VCExpressionGenerator.AndOp, instances.Values.ToList());
        if (exprTranslator.GenerationOptions.Options.KeepQuantifier)
        {
          return vcExprGen.And(quantifierExpr, instantiatedConjuncts);
        }
        else
        {
          return instantiatedConjuncts;
        }
      }
      else
      {
        var instantiatedDisjuncts = vcExprGen.NAry(VCExpressionGenerator.OrOp, instances.Values.ToList());
        if (exprTranslator.GenerationOptions.Options.KeepQuantifier)
        {
          return vcExprGen.Or(quantifierExpr, instantiatedDisjuncts);
        }
        else
        {
          return instantiatedDisjuncts;
        }
      }
    }

    private void InstantiateLambdaDefinition(Function lambdaFunction)
    {
      var quantifierExpr = lambdaDefinition[lambdaFunction];
      var boundVariableToLabels = quantifierExpr.Info.instantiationLabels;
      var boundVariableToExprs = boundVariableToLabels.Keys.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          boundVariableToLabels[boundVariable]
            .SelectMany(label =>
              accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<VCExpr>()).ToHashSet());
      foreach (var instance in accLambdaToInstances[lambdaFunction])
      {
        ConstructInstances(quantifierExpr, boundVariableToExprs, lambdaFunction.InParams.Count, instance);
      }
    }

    private void InstantiateQuantifier(VCExprQuantifier quantifierExpr)
    {
      var boundVariableToLabels = quantifierExpr.Info.instantiationLabels;
      var boundVariableToExprs = boundVariableToLabels.Keys.ToDictionary(
        boundVariable => boundVariable,
        boundVariable =>
          boundVariableToLabels[boundVariable]
            .SelectMany(label =>
              accLabelToInstances.ContainsKey(label) ? accLabelToInstances[label] : new HashSet<VCExpr>()).ToHashSet());
      ConstructInstances(quantifierExpr, boundVariableToExprs, 0, new List<VCExpr>());
    }

    private void ConstructInstances(VCExprQuantifier quantifierExpr,
      Dictionary<VCExprVar, HashSet<VCExpr>> boundVariableToExprs, int n, List<VCExpr> instance)
    {
      if (quantifierExpr.BoundVars.Count == n)
      {
        InstantiateQuantifierAtInstance(quantifierExpr, instance);
        return;
      }
      var boundVariable = quantifierExpr.BoundVars[n];
      foreach (var expr in boundVariableToExprs[boundVariable])
      {
        instance.Add(expr);
        ConstructInstances(quantifierExpr, boundVariableToExprs, n + 1, instance);
        instance.RemoveAt(n);
      }
    }

    private void InstantiateQuantifierAtInstance(VCExprQuantifier quantifierExpr, List<VCExpr> instance)
    {
      var quantifierInstantiationInfo = this.quantifierInstantiationInfo[quantifierExpr];
      if (quantifierInstantiationInfo.instances.ContainsKey(instance))
      {
        return;
      }

      // Since a pool name may be used with multiple types, we have to prune invalid instances
      for (int i = 0; i < quantifierExpr.BoundVars.Count; i++)
      {
        if (!quantifierExpr.BoundVars[i].Type.Equals(instance[i].Type))
        {
          return;
        }
      }

      var subst = new VCExprSubstitution(
        Enumerable.Range(0, quantifierExpr.BoundVars.Count).ToDictionary(
          x => quantifierExpr.BoundVars[x],
          x => instance[x]), new Dictionary<TypeVariable, Type>());
      var substituter = new SubstitutingVCExprVisitor(vcExprGen);
      var instantiation = substituter.Mutate(quantifierExpr.Body, subst);
      quantifierInstantiationInfo.instances[new List<VCExpr>(instance)] =
        Skolemizer.Skolemize(this, quantifierExpr.Quan == Quantifier.ALL ? Polarity.Positive : Polarity.Negative,
          instantiation);
    }
  }

  enum Polarity
  {
    Positive,
    Negative,
    Unknown,
  }
  
  class QuantifierCollector : BoundVarTraversingVCExprVisitor<Dictionary<VCExprVar, Polarity>, Polarity>
  {
    /*
     * This method collects quantifiers embedded in vcExpr.
     * If polarity == Polarity.Negative, a quantifier F embedded in expr is collected
     * if it can be proved that F is a forall quantifier in the NNF version of expr.
     * If polarity == Polarity.Positive, a quantifier F embedded in expr is collected
     * if it can be proved that F is an exists quantifier in the NNF version of expr.
     */
    public static HashSet<VCExprQuantifier> CollectQuantifiers(VCExpr vcExpr, Polarity polarity)
    {
      var visitor = new QuantifierCollector();
      visitor.Traverse(vcExpr, polarity);
      return visitor.quantifiers;
    }

    public static Polarity Flip(Polarity polarity)
    {
      switch (polarity)
      {
        case Polarity.Positive:
          return Polarity.Negative;
        case Polarity.Negative:
          return Polarity.Positive;
        case Polarity.Unknown:
          return Polarity.Unknown;
      }
      Contract.Assert(false);
      return Polarity.Unknown;
    }

    private HashSet<VCExprQuantifier> quantifiers = new HashSet<VCExprQuantifier>();
    
    private static Polarity Join(Polarity first, Polarity second)
    {
      if (first == second)
      {
        return first;
      }
      return Polarity.Unknown;
    }

    private static Dictionary<VCExprVar, Polarity> Join(IEnumerable<Dictionary<VCExprVar, Polarity>> elems)
    {
      var result = new Dictionary<VCExprVar, Polarity>();
      foreach (var elem in elems)
      {
        foreach (var x in elem.Keys)
        {
          if (result.ContainsKey(x))
          {
            result[x] = Join(result[x], elem[x]);
          }
          else
          {
            result[x] = elem[x];
          }
        }
      }
      return result;
    }
    
    private static Dictionary<VCExprVar, Polarity> Join(params Dictionary<VCExprVar, Polarity>[] elems)
    {
      return Join(elems.Select(x => x));
    }
    
    public override Dictionary<VCExprVar, Polarity> Visit(VCExprNAry node, Polarity arg)
    {
      if (arg != Polarity.Unknown)
      {
        if (node.Op.Equals(VCExpressionGenerator.NotOp))
        {
          return node[0].Accept(this, Flip(arg));
        }
        if (node.Op.Equals(VCExpressionGenerator.AndOp) || node.Op.Equals(VCExpressionGenerator.OrOp))
        {
          return Join(node[0].Accept(this, arg), node[1].Accept(this, arg));
        }
        if (node.Op.Equals(VCExpressionGenerator.ImpliesOp))
        {
          return Join(node[0].Accept(this, Flip(arg)), node[1].Accept(this, arg));
        }
      }
      return Join(node.UniformArguments.Select(x => x.Accept(this, Polarity.Unknown)));
    }

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprVar node, Polarity arg)
    {
      return new Dictionary<VCExprVar, Polarity> {{node, arg}};
    }

    protected override Dictionary<VCExprVar, Polarity> VisitAfterBinding(VCExprLet node, Polarity arg)
    {
      var result = node.Body.Accept(this, arg);
      for (int i = node.Length - 1; i >= 0; i--)
      {
        if (result.ContainsKey(node[i].V))
        {
          result = Join(result, node[i].E.Accept(this, result[node[i].V]));
        }
      }
      foreach (var x in node.BoundVars)
      {
        result.Remove(x);
      }
      return result;
    }

    protected override Dictionary<VCExprVar, Polarity> VisitAfterBinding(VCExprQuantifier node, Polarity arg)
    {
      var result = node.Body.Accept(this, arg);
      foreach (var x in node.BoundVars)
      {
        result.Remove(x);
      }
      return result;
    }

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprQuantifier node, Polarity arg)
    {
      var result = base.Visit(node, arg);
      if (arg != Polarity.Unknown && !result.Keys.Intersect(BoundTermVars.Keys).Any())
      {
        if ((arg == Polarity.Positive) == (node.Quan == Quantifier.EX))
        {
          quantifiers.Add(node);
        }
      }
      return result;
    }

    protected override Dictionary<VCExprVar, Polarity> StandardResult(VCExpr node, Polarity arg)
    {
      return null;
    }

    public override Dictionary<VCExprVar, Polarity> Visit(VCExprLiteral node, Polarity arg)
    {
      return new Dictionary<VCExprVar, Polarity>();
    }
  }
  
  class Skolemizer : MutatingVCExprVisitor<bool>
  {
    /*
     * The method Skolemize performs best-effort skolemization of the input expression expr.
     * Factorization is performed on the resulting expression.
     */
    public static VCExpr Skolemize(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr)
    {
      var skolemizer = new Skolemizer(qiEngine, polarity, vcExpr);
      var skolemizedExpr = skolemizer.Mutate(vcExpr, true);
      LambdaInstanceCollector.CollectInstances(qiEngine, vcExpr);
      return Factorizer.Factorize(qiEngine, skolemizedExpr);
    }

    private Skolemizer(QuantifierInstantiationEngine qiEngine, Polarity polarity, VCExpr vcExpr) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
      this.quantifiers = QuantifierCollector.CollectQuantifiers(vcExpr, polarity);
      this.bound = new Dictionary<VCExprVar, VCExpr>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprQuantifier> quantifiers;
    private Dictionary<VCExprVar, VCExpr> bound;

    public override VCExpr Visit(VCExprVar node, bool arg)
    {
      if (bound.ContainsKey(node))
      {
        return bound[node];
      }
      return base.Visit(node, arg);
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      if (node.TypeParameters.Count == 0 && quantifiers.Contains(node))
      {
        return PerformSkolemization(node, arg);
      }
      return base.Visit(node, arg);
    }

    private VCExpr PerformSkolemization(VCExprQuantifier node, bool arg)
    {
      var oldToNew = node.BoundVars.ToDictionary(v => v, v => (VCExpr) qiEngine.FreshSkolemConstant(v));
      foreach (var x in node.BoundVars)
      {
        bound.Add(x, oldToNew[x]);
      }
      var retExpr = (VCExprQuantifier) base.Visit(node, arg);
      retExpr.Info.instantiationExprs.ForEach(kv =>
      {
        CollectionExtensions.ForEach(kv.Value, expr => { qiEngine.AddTerm(kv.Key, expr.Accept(this, arg)); });
      });
      foreach (var x in node.BoundVars)
      {
        bound.Remove(x);
      }
      return retExpr.Body;
    }
  }
  
  class Factorizer : MutatingVCExprVisitor<bool>
  {
    /* 
     * The method Factorize factors out quantified expressions in expr replacing them with a bound variable.
     * The binding between the bound variable and the quantifier replaced by it is registered in qiEngine.
     */
    
    private QuantifierInstantiationEngine qiEngine;

    public static VCExpr Factorize(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr)
    {
      var factorizer = new Factorizer(qiEngine);
      return factorizer.Mutate(vcExpr, true);
    }

    private Factorizer(QuantifierInstantiationEngine qiEngine) : base(qiEngine.vcExprGen)
    {
      this.qiEngine = qiEngine;
    }

    public override VCExpr Visit(VCExprQuantifier node, bool arg)
    {
      return qiEngine.BindQuantifier(node);
    }
  }
  
  class BindingCollector : TraversingVCExprVisitor<bool, bool>
  {
    public static HashSet<VCExprVar> CollectBindings(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr)
    {
      var bindingCollector = new BindingCollector(qiEngine);
      bindingCollector.Traverse(vcExpr, true);
      return bindingCollector.bindings;
    }

    private BindingCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.bindings = new HashSet<VCExprVar>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprVar> bindings;

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      if (qiEngine.IsQuantifierBinding(node))
      {
        bindings.Add(node);
      }
      return base.Visit(node, arg);
    }
  }
  
  class LambdaInstanceCollector : BoundVarTraversingVCExprVisitor<bool, bool>
  {
    public static void CollectInstances(QuantifierInstantiationEngine qiEngine, VCExpr vcExpr)
    {
      var lambdaInstanceCollector = new LambdaInstanceCollector(qiEngine);
      lambdaInstanceCollector.Traverse(vcExpr, true);
      var lambdaFunctionToInstances = new Dictionary<Function, HashSet<List<VCExpr>>>();
      foreach (var instance in lambdaInstanceCollector.instances)
      {
        var function = (instance.Op as VCExprBoogieFunctionOp).Func;
        if (!lambdaFunctionToInstances.ContainsKey(function))
        {
          lambdaFunctionToInstances[function] = new HashSet<List<VCExpr>>(new ListComparer<VCExpr>());
        }
        lambdaFunctionToInstances[function].Add(instance.UniformArguments.ToList());
      }
      qiEngine.AddLambdaInstances(lambdaFunctionToInstances);
    }

    private LambdaInstanceCollector(QuantifierInstantiationEngine qiEngine)
    {
      this.qiEngine = qiEngine;
      this.instances = new HashSet<VCExprNAry>();
      this.instancesOnStack = new Stack<Tuple<VCExprNAry, HashSet<VCExprVar>>>();
      this.letBoundVarsOnStack = new Stack<List<VCExprVar>>();
    }

    private QuantifierInstantiationEngine qiEngine;
    private HashSet<VCExprNAry> instances;
    private Stack<Tuple<VCExprNAry, HashSet<VCExprVar>>> instancesOnStack;
    private Stack<List<VCExprVar>> letBoundVarsOnStack;

    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }

    private VCExprNAry Substitute(VCExprNAry vcExpr)
    {
      foreach (var letBoundVars in letBoundVarsOnStack)
      {
        var subst = new VCExprSubstitution(
          letBoundVars.ToDictionary(x => x, x => BoundTermVars[x]),
          new Dictionary<TypeVariable, Type>());
        var substituter = new SubstitutingVCExprVisitor(qiEngine.vcExprGen);
        vcExpr = (VCExprNAry) substituter.Mutate(vcExpr, subst);
      }
      return vcExpr;
    }
    
    public override bool Visit(VCExprNAry node, bool arg)
    {
      if (node.Op is VCExprBoogieFunctionOp functionOp)
      {
        var function = functionOp.Func;
        if (function.OriginalLambdaExprAsString != null && qiEngine.BindLambdaFunction(function))
        {
          // substitute all let-bound variables in the lambda expr
          var substExpr = Substitute(node);
          instances.Add(substExpr);
          // push the pair of substituted lambda expr and variables bound via quantifiers
          // if one of these bound variables is mentioned in the lambda term,
          // then this term is ineligible and should be removed
          instancesOnStack.Push(new Tuple<VCExprNAry, HashSet<VCExprVar>>(substExpr,
            BoundTermVars.Keys.Where(x => BoundTermVars[x] == null).ToHashSet()));
          var retVal = base.Visit(node, arg);
          instancesOnStack.Pop();
          return retVal;
        }
      }
      return base.Visit(node, arg);
    }

    public override bool Visit(VCExprVar node, bool arg)
    {
      // check each lambda term going down the stack and remove ineligible terms if any
      // once an eligible term is found, all terms below it must be eligible as well
      foreach (var pair in instancesOnStack)
      {
        if (pair.Item2.Contains(node))
        {
          instances.Remove(pair.Item1);
        }
        else
        {
          break;
        }
      }
      return base.Visit(node, arg);
    }
    
    public override bool Visit(VCExprLet node, bool arg)
    {
      letBoundVarsOnStack.Push(node.BoundVars);
      var retVal = base.Visit(node, arg);
      letBoundVarsOnStack.Pop();
      return retVal;
    }
  }
  
  class InstantiationSourceChecker : ReadOnlyVisitor
  {
    private bool hasInstances;

    private void FindInstantiationSources(ICarriesAttributes o)
    {
      var iter = o.Attributes;
      while (iter != null)
      {
        if (iter.Key == "add_to_pool")
        {
          if (iter.Params[0] is string poolName && QuantifierInstantiationEngine.labelToTypes.ContainsKey(poolName))
          {
            var tok = iter.tok;
            var poolTypes = QuantifierInstantiationEngine.labelToTypes[poolName];
            iter.Params.Skip(1).ForEach(x =>
            {
              if (x is Expr e && poolTypes.Contains(e.Type))
              {
                hasInstances = true;
              }
            });
          }
        }
        iter = iter.Next;
      }
    }
    
    public static bool HasInstantiationSources(Implementation impl)
    {
      var instanceChecker = new InstantiationSourceChecker();
      instanceChecker.VisitImplementation(impl);
      return instanceChecker.hasInstances;
    }

    private InstantiationSourceChecker()
    {
      this.hasInstances = false;
    }
    
    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
      FindInstantiationSources(node);
      return base.VisitQuantifierExpr(node);
    }

    public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
    {
      cmdSeq.OfType<PredicateCmd>().ForEach(FindInstantiationSources);
      return base.VisitCmdSeq(cmdSeq);
    }
  }
}
