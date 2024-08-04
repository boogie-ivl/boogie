using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;
using Set = Microsoft.Boogie.GSet<object>;

namespace Core
{
  /// <summary>
  /// This visitor performs the first phase of the MaxHoles lambda lifting (see <see cref="LambdaHelper.ExpandLambdas"/>),
  /// after which it invokes the second phase in the <see cref="VisitLambdaExpr"/> method.
  /// This phase consists of generating a "template" for each subexpression of the lambda. A template is an expression
  /// that contains "holes", which will be the maximally large subexpressions that do not contain the lambda's bound
  /// variables.
  ///
  /// To encode templates we store a <see cref="_templates"/> dictionary that maps each node to its template,
  /// an object of type <see cref="LambdaLiftingTemplate"/>.
  ///
  /// The first phase traverses a lambda's AST bottom-up, pupulating the <see cref="_templates"/> map.
  /// At the end of the first phase, we obtain a list of replacement expressions that correspond to the holes in
  /// the lambda.
  ///
  /// The second phase replaces the templates with bound variables. It is handled by the
  /// <see cref="LambdaLiftingMaxHolesFiller.Fill"/> method.
  ///
  /// This class requires a lambda's `old` expressions to occur only around free variables (this
  /// transformation is performed in <c>LambdaHelper.LiftLambdaMaxHoles</c>). 
  /// </summary>
  class MaxHolesLambdaLifter : StandardVisitor
  {
    private CoreOptions options;
    private readonly List<Variable> _nestedBoundVariables = new List<Variable>();

    private readonly LambdaExpr _lambda;
    private readonly LiftedLambdas _liftedLambdas;
    private readonly String _freshFnName;
    private readonly List<Function> _lambdaFunctions;
    private readonly List<Axiom> _lambdaAxioms;
    private int _freshVarCount;

    private readonly Dictionary<Absy, LambdaLiftingTemplate> _templates = new Dictionary<Absy, LambdaLiftingTemplate>();

    public MaxHolesLambdaLifter(
      LambdaExpr lambda,
      LiftedLambdas liftedLambdas,
      string freshFnName,
      List<Function> lambdaFunctions,
      List<Axiom> lambdaAxioms, CoreOptions options, int freshVarCount = 0
    )
    {
      _lambda = lambda;
      _liftedLambdas = liftedLambdas;
      _freshFnName = freshFnName;
      _lambdaFunctions = lambdaFunctions;
      _lambdaAxioms = lambdaAxioms;
      this.options = options;
      _freshVarCount = freshVarCount;
    }

    private string FreshVarNameGen(List<string> existing)
    {
      var prefix = "l#";
      while (true)
      {
        var newName = prefix + _freshVarCount;
        _freshVarCount++;
        if (!existing.Contains(newName))
        {
          return newName;
        }
      }
    }

    private bool IsBound(Variable node)
    {
      return _lambda.Dummies.Contains(node) || _nestedBoundVariables.Contains(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      base.VisitNAryExpr(node);
      var nodeArgs = node.Args;
      if (nodeArgs.Any(arg => _templates[arg].ContainsBoundVariables()))
      {
        var replacements = new List<Expr>();
        foreach (Expr arg in nodeArgs)
        {
          replacements.AddRange(_templates[arg].GetReplacements());
        }

        _templates[node] = new TemplateWithBoundVariables(replacements);
      }
      else
      {
        var newArgs = from arg in nodeArgs select ((TemplateNoBoundVariables) _templates[arg]).GetReplacement();
        var llReplacementExpr =
          new NAryExpr(node.tok, node.Fun, newArgs.ToList(), node.Immutable)
          {
            TypeParameters = node.TypeParameters
          };
        llReplacementExpr.Type = node.Type ?? node.ShallowType;
        _templates[node] = new TemplateNoBoundVariables(llReplacementExpr);
      }

      return node;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      base.VisitIdentifierExpr(node);
      if (IsBound(node.Decl))
      {
        _templates[node] = new TemplateWithBoundVariables();
      }
      else
      {
        _templates[node] = _templates[node.Decl];
      }

      return node;
    }

    public override Expr VisitLiteralExpr(LiteralExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      base.VisitLiteralExpr(node);
      _templates[node] = new TemplateNoBoundVariables(node);
      return node;
    }

    public override Expr VisitLetExpr(LetExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      _nestedBoundVariables.AddRange(node.Dummies);
      base.VisitLetExpr(node);
      var bodyTemplate = _templates[node.Body];
      var varBodies = node.Rhss;
      if (bodyTemplate.ContainsBoundVariables() || varBodies.Any(body => _templates[body].ContainsBoundVariables()))
      {
        var replacements = new List<Expr>();
        foreach (Expr body in varBodies)
        {
          replacements.AddRange(_templates[body].GetReplacements());
        }

        replacements.AddRange(bodyTemplate.GetReplacements());
        _templates[node] = new TemplateWithBoundVariables(replacements);
      }
      else
      {
        var newRhss = from arg in varBodies select ((TemplateNoBoundVariables) _templates[arg]).GetReplacement();
        LambdaLiftingTemplate template = new TemplateNoBoundVariables(
          new LetExpr(node.tok, node.Dummies, newRhss.ToList(),
            node.Attributes,
            ((TemplateNoBoundVariables) _templates[node.Body])
            .GetReplacement()) {Type = node.Type});
        _templates[node] = template;
      }

      return node;
    }

    public override Expr VisitForallExpr(ForallExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      _nestedBoundVariables.AddRange(node.Dummies);
      base.VisitForallExpr(node);
      var body = node.Body;
      var bodyTemplate = _templates[body];
      var trigger = node.Triggers;
      var triggerNoBounds = trigger == null || !_templates[trigger].ContainsBoundVariables();
      if (bodyTemplate is TemplateNoBoundVariables bt && triggerNoBounds)
      {
        var newBody = bt.GetReplacement();
        var newTrigger = ReplacementTrigger(trigger);
        _templates[node] = new TemplateNoBoundVariables(
          new ForallExpr(node.tok, node.TypeParameters, node.Dummies, node.Attributes, newTrigger,
            newBody, node.Immutable) {Type = node.Type});
      }
      else
      {
        var replacements = bodyTemplate.GetReplacements();
        if (trigger != null)
        {
          replacements.AddRange(_templates[trigger].GetReplacements());
        }

        _templates[node] = new TemplateWithBoundVariables(replacements);
      }

      return node;
    }

    public override Expr VisitExistsExpr(ExistsExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      _nestedBoundVariables.AddRange(node.Dummies);
      base.VisitExistsExpr(node);
      var body = node.Body;
      var bodyTemplate = _templates[body];
      var trigger = node.Triggers;
      var triggerNoBounds = trigger == null || !_templates[trigger].ContainsBoundVariables();
      if (bodyTemplate is TemplateNoBoundVariables bt && triggerNoBounds)
      {
        var newBody = bt.GetReplacement();
        var newTrigger = ReplacementTrigger(trigger);
        _templates[node] = new TemplateNoBoundVariables(
          new ExistsExpr(node.tok, node.TypeParameters, node.Dummies, node.Attributes, newTrigger, newBody,
            node.Immutable) {Type = node.Type});
      }
      else
      {
        var replacements = bodyTemplate.GetReplacements();
        if (trigger != null)
        {
          replacements.AddRange(_templates[trigger].GetReplacements());
        }

        _templates[node] = new TemplateWithBoundVariables(replacements);
      }

      return node;
    }

    private List<Expr> QKeyValueReplacements(QKeyValue node)
    {
      Contract.Requires(node != null);
      var ts = (from e in node.Params where e != null && e is Expr select _templates[e as Expr]).ToList();
      var replacements = new List<Expr>();
      foreach (LambdaLiftingTemplate llt in ts)
      {
        replacements.AddRange(llt.GetReplacements());
      }

      replacements.AddRange(node.Next == null ? new List<Expr>() : QKeyValueReplacements(node.Next));
      return replacements;
    }

    private Trigger ReplacementTrigger(Trigger trigger)
    {
      if (trigger == null)
      {
        return null;
      }

      var replacements = _templates[trigger].GetReplacements();
      var next = trigger.Next;
      return new Trigger(trigger.tok, trigger.Pos, replacements, next == null ? null : ReplacementTrigger(next));
    }

    public override Trigger VisitTrigger(Trigger node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      base.VisitTrigger(node);
      var templates = (from e in node.Tr select _templates[e]).ToList();
      var replacements = new List<Expr>();
      if (node.Next != null)
      {
        // the replacements for .Next must be added first, since the standard visitor visits them first
        replacements.AddRange(_templates[node.Next].GetReplacements());
      }

      foreach (LambdaLiftingTemplate llt in templates)
      {
        replacements.AddRange(llt.GetReplacements());
      }

      var nextNoBounds = node.Next == null || !_templates[node.Next].ContainsBoundVariables();
      if (nextNoBounds && templates.All(r => !r.ContainsBoundVariables()))
      {
        _templates[node] = new TemplateNoBoundVariablesTriggerOrKv(replacements);
      }
      else
      {
        _templates[node] = new TemplateWithBoundVariables(replacements);
      }

      return node;
    }

    public override Expr VisitLambdaExpr(LambdaExpr node)
    {
      // Phase I of the lambda lifting
      base.VisitLambdaExpr(node);
      if (node.Attributes != null)
      {
        VisitQKeyValue(node.Attributes);
      }

      // Phase II of the lambda lifting.
      var attribReplacementExprs =
        node.Attributes == null ? new List<Expr>() : QKeyValueReplacements(node.Attributes);
      var llReplacementExprs = _templates[node.Body].GetReplacements();
      var allReplacementExprs = new List<Expr>(attribReplacementExprs);
      allReplacementExprs.AddRange(llReplacementExprs);
      var typedIdents = (from replExpr in allReplacementExprs
          select new TypedIdent(replExpr.tok, FreshVarNameGen(new List<string>()),
            replExpr.Type ?? replExpr.ShallowType))
        .ToList();
      var formals = allReplacementExprs.Zip(typedIdents,
        (replExpr, typedIdent) => (Variable) new Formal(replExpr.tok, typedIdent, true));
      var replDummies = allReplacementExprs.Zip(typedIdents,
        (replExpr, typedIdent) => (Variable) new BoundVariable(replExpr.tok, typedIdent)).ToList();
      var replDummyIds = (from dummy in replDummies select (Expr) new IdentifierExpr(dummy.tok, dummy)).ToList();
      var dummies = new List<Variable>(replDummies);
      dummies.AddRange(_lambda.Dummies);


      var lambdaAttrs = _lambda.Attributes;
      if (0 < options.VerifySnapshots && QKeyValue.FindStringAttribute(lambdaAttrs, "checksum") == null)
      {
        // Attach a dummy checksum to avoid issues in the dependency analysis.
        var checksumAttr = new QKeyValue(_lambda.tok, "checksum", new List<object> {"lambda expression"}, null);
        if (lambdaAttrs == null)
        {
          lambdaAttrs = checksumAttr;
        }
        else
        {
          lambdaAttrs.AddLast(checksumAttr);
        }
      }

      Set freeVars = new Set();
      BinderExpr.ComputeBinderFreeVariables(_lambda.TypeParameters, _lambda.Dummies, _lambda.Body, null, lambdaAttrs,
        freeVars);
      var freeTypeVars = freeVars.OfType<TypeVariable>().ToList();
      var freeVarActuals = freeVars.OfType<Type>().ToList();

      var sw = new StringWriter();
      var wr = new TokenTextWriter(sw, true, options);
      _lambda.Emit(wr);
      string lam_str = sw.ToString();

      // the resulting lifted function applied to free variables
      IToken tok = _lambda.tok;
      Formal res = new Formal(tok, new TypedIdent(tok, TypedIdent.NoName, Cce.NonNull(_lambda.Type)), false);

      var liftedLambda = (LambdaExpr) LambdaLiftingMaxHolesFiller.Fill(
        (from kvp in _templates where !kvp.Value.ContainsBoundVariables() select kvp.Key).ToList(),
        replDummies, _lambda, lambdaAttrs);

      if (_liftedLambdas.TryGetValue(liftedLambda, out var fcall))
      {
        if (options.TraceVerify)
        {
          options.OutputWriter.WriteLine("Old lambda: {0}", lam_str);
        }
      }
      else
      {
        if (options.TraceVerify)
        {
          options.OutputWriter.WriteLine("New lambda: {0}", lam_str);
        }

        var freshTypeVars = (from tv in freeTypeVars select new TypeVariable(tv.tok, tv.Name)).ToList();
        // this will be the lifted function that takes free variables as arguments
        Function fn = new Function(tok, _freshFnName, freshTypeVars, formals.ToList(), res,
          "auto-generated lambda function", liftedLambda.Attributes) {OriginalLambdaExprAsString = lam_str};

        fcall = new FunctionCall(new IdentifierExpr(tok, fn.Name));
        fcall.Func = fn;
        _liftedLambdas[liftedLambda] = fcall;

        // the arguments to the select map (the map that will be equal to the lifted lambda)
        List<Expr> selectArgs = new List<Expr>();
        foreach (Variable v in _lambda.Dummies)
        {
          Contract.Assert(v != null);
          selectArgs.Add(new IdentifierExpr(v.tok, v));
        }

        NAryExpr axcall = new NAryExpr(tok, fcall, replDummyIds)
        {
          Type = res.TypedIdent.Type,
          TypeParameters = SimpleTypeParamInstantiation.From(freeTypeVars, freeVarActuals)
        };
        // the Boogie map, applied to selectArgs, will be equal to the lifted lambda call
        NAryExpr select = Expr.Select(axcall, selectArgs);
        select.Type = _lambda.Body.Type;
        List<Type> selectTypeParamActuals = new List<Type>();
        List<TypeVariable> forallTypeVariables = new List<TypeVariable>();
        foreach (TypeVariable tp in _lambda.TypeParameters)
        {
          Contract.Assert(tp != null);
          selectTypeParamActuals.Add(tp);
          forallTypeVariables.Add(tp);
        }

        forallTypeVariables.AddRange(freeTypeVars);
        select.TypeParameters = SimpleTypeParamInstantiation.From(_lambda.TypeParameters, selectTypeParamActuals);
        
        NAryExpr body = Expr.Eq(select, liftedLambda.Body);
        body.Type = Type.Bool;
        body.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
        var trig = new Trigger(select.tok, true, new List<Expr> {select});

        _lambdaFunctions.Add(fn);
        fn.DefinitionAxiom = new Axiom(tok, new ForallExpr(tok, forallTypeVariables, dummies, liftedLambda.Attributes, trig, body));
        _lambdaAxioms.Add(fn.DefinitionAxiom);
      }

      NAryExpr call = new NAryExpr(tok, fcall, allReplacementExprs.ToList())
      {
        Type = res.TypedIdent.Type, TypeParameters = SimpleTypeParamInstantiation.From(freeTypeVars, freeVarActuals)
      };

      return call;
    }

    public override Variable VisitVariable(Variable node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      base.VisitVariable(node);
      if (IsBound(node))
      {
        _templates[node] = new TemplateWithBoundVariables();
      }
      else
      {
        var identifierExpr = new IdentifierExpr(node.tok, node);
        identifierExpr.Type = node.TypedIdent.Type;
        _templates[node] = new TemplateNoBoundVariables(identifierExpr);
      }

      return node;
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
      Contract.Requires(node != null);
      if (_templates.ContainsKey(node))
      {
        return node;
      }

      base.VisitOldExpr(node);
      if (_templates[node.Expr] is TemplateNoBoundVariables t)
      {
        var replacement = t.GetReplacement();
        var llReplacement = new OldExpr(replacement.tok, replacement) {Type = replacement.Type};
        _templates[node] = new TemplateNoBoundVariables(llReplacement);
      }
      else
      {
        // After OldFinder pass, old expressions should only occur around free variables
        throw new Cce.UnreachableException();
      }

      return node;
    }
  }
}