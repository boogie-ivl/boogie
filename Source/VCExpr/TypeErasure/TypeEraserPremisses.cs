using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

public class TypeEraserPremisses : TypeEraser
{
  private readonly TypeAxiomBuilderPremisses /*!*/ AxBuilderPremisses;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(AxBuilderPremisses != null);
  }


  private OpTypeEraser OpEraserAttr = null;

  protected override OpTypeEraser /*!*/ OpEraser
  {
    get
    {
      Contract.Ensures(Contract.Result<OpTypeEraser>() != null);

      if (OpEraserAttr == null)
      {
        OpEraserAttr = new OpTypeEraserPremisses(this, AxBuilderPremisses, Gen);
      }

      return OpEraserAttr;
    }
  }

  public TypeEraserPremisses(TypeAxiomBuilderPremisses axBuilder, VCExpressionGenerator gen)
    : base(axBuilder, gen)
  {
    Contract.Requires(gen != null);
    Contract.Requires(axBuilder != null);

    this.AxBuilderPremisses = axBuilder;
  }

  ////////////////////////////////////////////////////////////////////////////

  public override VCExpr Visit(VCExprQuantifier node, VariableBindings oldBindings)
  {
    Contract.Requires(oldBindings != null);
    Contract.Requires(node != null);
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    VariableBindings bindings = oldBindings.Clone();

    // determine the bound vars that actually occur in the body or
    // in any of the triggers (if some variables do not occur, we
    // need to take special care of type parameters that only occur
    // in the types of such variables)
    FreeVariableCollector coll = new FreeVariableCollector();
    coll.Collect(node.Body);
    foreach (VCTrigger trigger in node.Triggers)
    {
      if (trigger.Pos)
      {
        foreach (VCExpr /*!*/ e in trigger.Exprs)
        {
          Contract.Assert(e != null);

          coll.Collect(e);
        }
      }
    }

    List<VCExprVar /*!*/> occurringVars = new List<VCExprVar /*!*/>(node.BoundVars.Count);
    foreach (VCExprVar var in node.BoundVars)
    {
      if (coll.FreeTermVars.Contains(var))
      {
        occurringVars.Add(var);
      }
    }

    occurringVars.TrimExcess();

    // bound term variables are replaced with bound term variables typed in
    // a simpler way
    List<VCExprVar /*!*/> /*!*/
      newBoundVars =
        BoundVarsAfterErasure(occurringVars, bindings);
    Contract.Assert(Cce.NonNullElements(newBoundVars));
    VCExpr /*!*/
      newNode = HandleQuantifier(node, occurringVars,
        newBoundVars, bindings);
    Contract.Assert(newNode != null);

    if (!(newNode is VCExprQuantifier) || !IsUniversalQuantifier(node))
    {
      return newNode;
    }

    if (!RedoQuantifier(node, (VCExprQuantifier) newNode, occurringVars, oldBindings,
          out var bindings2, out newBoundVars))
    {
      return newNode;
    }

    return HandleQuantifier(node, occurringVars,
      newBoundVars, bindings2);
  }

  private VCExpr /*!*/ GenTypePremisses(List<VCExprVar /*!*/> /*!*/ oldBoundVars,
    List<VCExprVar /*!*/> /*!*/ newBoundVars,
    IDictionary<TypeVariable /*!*/, VCExpr /*!*/> /*!*/
      typeVarTranslation,
    List<VCExprLetBinding /*!*/> /*!*/ typeVarBindings,
    out List<VCTrigger /*!*/> /*!*/ triggers)
  {
    Contract.Requires(Cce.NonNullElements(oldBoundVars));
    Contract.Requires(Cce.NonNullElements(newBoundVars));
    Contract.Requires(Cce.NonNullDictionaryAndValues(typeVarTranslation));
    Contract.Requires(Cce.NonNullElements(typeVarBindings));
    Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out triggers)));
    Contract.Ensures(Contract.Result<VCExpr>() != null);

    // build a substitution of the type variables that it can be checked
    // whether type premisses are trivial
    VCExprSubstitution /*!*/
      typeParamSubstitution = new VCExprSubstitution();
    foreach (VCExprLetBinding /*!*/ binding in typeVarBindings)
    {
      Contract.Assert(binding != null);
      typeParamSubstitution[binding.V] = binding.E;
    }

    SubstitutingVCExprVisitor /*!*/
      substituter = new SubstitutingVCExprVisitor(Gen);
    Contract.Assert(substituter != null);

    List<VCExpr /*!*/> /*!*/
      typePremisses = new List<VCExpr /*!*/>(newBoundVars.Count);
    triggers = new List<VCTrigger /*!*/>(newBoundVars.Count);

    for (int i = 0; i < newBoundVars.Count; ++i)
    {
      VCExprVar /*!*/
        oldVar = oldBoundVars[i];
      Contract.Assert(oldVar != null);
      VCExprVar /*!*/
        newVar = newBoundVars[i];
      Contract.Assert(newVar != null);

      VCExpr /*!*/
        typePremiss =
          AxBuilderPremisses.GenVarTypeAxiom(newVar, oldVar.Type,
            typeVarTranslation);
      Contract.Assert(typePremiss != null);
      if (!IsTriviallyTrue(substituter.Mutate(typePremiss,
            typeParamSubstitution)))
      {
        typePremisses.Add(typePremiss);
        // generate a negative trigger for the variable occurrence
        // in the type premiss
        triggers.Add(Gen.Trigger(false,
          HelperFuns.ToList(AxBuilderPremisses.TypeOf(newVar))));
      }
    }

    typePremisses.TrimExcess();
    triggers.TrimExcess();

    return Gen.NAry(VCExpressionGenerator.AndOp, typePremisses);
  }

  // these optimisations should maybe be moved into a separate
  // visitor (peep-hole optimisations)
  private bool IsTriviallyTrue(VCExpr expr)
  {
    Contract.Requires(expr != null);
    if (expr.Equals(VCExpressionGenerator.True))
    {
      return true;
    }

    if (expr is VCExprNAry)
    {
      VCExprNAry /*!*/
        naryExpr = (VCExprNAry) expr;
      Contract.Assert(naryExpr != null);
      if (naryExpr.Op.Equals(VCExpressionGenerator.EqOp) &&
          naryExpr[0].Equals(naryExpr[1]))
      {
        return true;
      }
    }

    return false;
  }

  private VCExpr HandleQuantifier(VCExprQuantifier node, List<VCExprVar /*!*/> /*!*/ occurringVars /*!*/,
    List<VCExprVar /*!*/> /*!*/ newBoundVars, VariableBindings bindings)
  {
    Contract.Requires(bindings != null);
    Contract.Requires(node != null);
    Contract.Requires(Cce.NonNullElements(occurringVars /*!*/));
    Contract.Requires(Cce.NonNullElements(newBoundVars));
    Contract.Ensures(Contract.Result<VCExpr>() != null);
    List<VCExprLetBinding /*!*/> /*!*/
      typeVarBindings =
        AxBuilderPremisses.GenTypeParamBindings(node.TypeParameters, occurringVars, bindings, true);
    Contract.Assert(typeVarBindings != null);
    // Check whether some of the type parameters could not be
    // determined from the bound variable types. In this case, we
    // quantify explicitly over these variables
    if (typeVarBindings.Count < node.TypeParameters.Count)
    {
      foreach (TypeVariable /*!*/ var in node.TypeParameters)
      {
        Contract.Assert(var != null);
        if (typeVarBindings.All(b => !b.V.Equals(bindings.TypeVariableBindings[var])))
        {
          newBoundVars.Add((VCExprVar) bindings.TypeVariableBindings[var]);
        }
      }
    }

    // the lists of old and new bound variables for which type
    // antecedents are to be generated
    List<VCExprVar /*!*/> /*!*/
      varsWithTypeSpecs = new List<VCExprVar /*!*/>();
    List<VCExprVar /*!*/> /*!*/
      newVarsWithTypeSpecs = new List<VCExprVar /*!*/>();
    if (!IsUniversalQuantifier(node) ||
        AxBuilderPremisses.Options.TypeEncodingMethod
        == CoreOptions.TypeEncoding.Predicates)
    {
      foreach (VCExprVar /*!*/ oldVar in occurringVars)
      {
        Contract.Assert(oldVar != null);
        varsWithTypeSpecs.Add(oldVar);
        newVarsWithTypeSpecs.Add(bindings.VCExprVarBindings[oldVar]);
      }
    } // else, no type antecedents are created for any variables

    VCExpr /*!*/
      typePremisses =
        GenTypePremisses(varsWithTypeSpecs, newVarsWithTypeSpecs,
          bindings.TypeVariableBindings,
          typeVarBindings, out var furtherTriggers);

    Contract.Assert(Cce.NonNullElements(furtherTriggers));
    Contract.Assert(typePremisses != null);
    List<VCTrigger /*!*/> /*!*/
      newTriggers = new List<VCTrigger>(MutateTriggers(node.Triggers, bindings));
    Contract.Assert(Cce.NonNullElements(newTriggers));
    newTriggers.AddRange(furtherTriggers);
    newTriggers = AddLets2Triggers(newTriggers, typeVarBindings);

    VCExpr /*!*/
      newBody = Mutate(node.Body, bindings);
    Contract.Assert(newBody != null);

    // assemble the new quantified formula

    VCExpr /*!*/
      bodyWithPremisses =
        AxBuilderPremisses.AddTypePremisses(typeVarBindings, typePremisses,
          node.Quan == Quantifier.ALL,
          AxBuilder.Cast(newBody, Type.Bool));
    Contract.Assert(bodyWithPremisses != null);
    if (newBoundVars.Count == 0) // might happen that no bound variables are left
    {
      return bodyWithPremisses;
    }

    foreach (VCExprVar /*!*/ v in newBoundVars)
    {
      Contract.Assert(v != null);
      if (v.Type == AxBuilderPremisses.U)
      {
        newTriggers.Add(Gen.Trigger(false, AxBuilderPremisses.Cast(v, Type.Int)));
        newTriggers.Add(Gen.Trigger(false, AxBuilderPremisses.Cast(v, Type.Bool)));
      }
    }

    return Gen.Quantify(node.Quan, new List<TypeVariable /*!*/>(), newBoundVars,
      newTriggers, node.Info, bodyWithPremisses);
  }

  // check whether we need to add let-binders for any of the type
  // parameters to the triggers (otherwise, the triggers will
  // contain unbound/dangling variables for such parameters)
  private List<VCTrigger /*!*/> /*!*/ AddLets2Triggers(List<VCTrigger /*!*/> /*!*/ triggers /*!*/,
    List<VCExprLetBinding /*!*/> /*!*/ typeVarBindings)
  {
    Contract.Requires(Cce.NonNullElements(triggers /*!*/));
    Contract.Requires(Cce.NonNullElements(typeVarBindings));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCTrigger>>()));
    List<VCTrigger /*!*/> /*!*/
      triggersWithLets = new List<VCTrigger /*!*/>(triggers.Count);

    foreach (VCTrigger /*!*/ t in triggers)
    {
      Contract.Assert(t != null);
      List<VCExpr /*!*/> /*!*/
        exprsWithLets = new List<VCExpr /*!*/>(t.Exprs.Count);

      bool changed = false;
      foreach (VCExpr /*!*/ e in t.Exprs)
      {
        Contract.Assert(e != null);
        HashSet<VCExprVar> freeVars = FreeVariableCollector.FreeTermVariables(e);
        Contract.Assert(freeVars != null && Cce.NonNullElements(freeVars));
        if (typeVarBindings.Any(b => freeVars.Contains(b.V)))
        {
          exprsWithLets.Add(Gen.Let(typeVarBindings, e));
          changed = true;
        }
        else
        {
          exprsWithLets.Add(e);
        }
      }

      if (changed)
      {
        triggersWithLets.Add(Gen.Trigger(t.Pos, exprsWithLets));
      }
      else
      {
        triggersWithLets.Add(t);
      }
    }

    return triggersWithLets;
  }
}