using System.Diagnostics.Contracts;
using System.Collections.Generic;

// Visitor to search for types proxies that could not completely be
// determined by type inference. If this happens, a warning is
// generated and the proxies are instantiated in a more or less arbitrary
// fashion.

namespace Microsoft.Boogie
{
  public class TypeAmbiguitySeeker : ReadOnlyVisitor
  {
    private readonly InTypeSeeker /*!*/
      inTypeSeeker = new InTypeSeeker();

    private readonly TypecheckingContext /*!*/
      TC;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(inTypeSeeker != null);
      Contract.Invariant(TC != null);
    }


    public TypeAmbiguitySeeker(TypecheckingContext tc)
    {
      Contract.Requires(tc != null);
      TC = tc;
    }

    private void CheckTypeParams(Absy node, TypeParamInstantiation insts)
    {
      Contract.Requires(insts != null);
      Contract.Requires(node != null);
      foreach (TypeVariable /*!*/ var in insts.FormalTypeParams)
      {
        Contract.Assert(var != null);
        Type /*!*/
          inst = insts[var];
        Contract.Assert(inst != null);

        inTypeSeeker.FoundAmbiguity = false;
        inTypeSeeker.Visit(inst);
        if (inTypeSeeker.FoundAmbiguity)
        {
          TC.Warning(node,
            "type parameter {0} is ambiguous, instantiating to {1}",
            var, inst);
        }
      }
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Expr>() != null);
      CheckTypeParams(node, Cce.NonNull(node.TypeParameters));
      return base.VisitNAryExpr(node);
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<AssignLhs>() != null);
      CheckTypeParams(node, Cce.NonNull(node.TypeParameters));
      return base.VisitMapAssignLhs(node);
    }
  }

  internal class InTypeSeeker : ReadOnlyVisitor
  {
    internal bool FoundAmbiguity = false;

    // called when an uninstantiated proxy was found
    private Type Instantiate(Type node, Type inst)
    {
      Contract.Requires(inst != null);
      Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() == node);
      FoundAmbiguity = true;
      bool success = node.Unify(inst);
      Contract.Assert(success);
      return node;
    }

    public override Type VisitTypeProxy(TypeProxy node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      if (node.ProxyFor != null)
      {
        return base.VisitTypeProxy(node);
      }

      return Instantiate(node, Type.Int);
    }

    public override Type VisitMapTypeProxy(MapTypeProxy node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      if (node.ProxyFor != null)
      {
        return base.VisitMapTypeProxy(node);
      }

      List<TypeVariable> /*!*/
        typeParams = new List<TypeVariable>();
      List<Type> /*!*/
        arguments = new List<Type>();
      for (int i = 0; i < node.Arity; ++i)
      {
        TypeVariable /*!*/
          param = new TypeVariable(Token.NoToken, "arg" + i);
        Contract.Assert(param != null);
        typeParams.Add(param);
        arguments.Add(param);
      }

      TypeVariable /*!*/
        result = new TypeVariable(Token.NoToken, "res");
      Contract.Assert(result != null);
      typeParams.Add(result);

      Type /*!*/
        instantiation = new MapType(Token.NoToken, typeParams, arguments, result);
      Contract.Assert(instantiation != null);

      return Instantiate(node, instantiation);
    }

    public override Type VisitBvTypeProxy(BvTypeProxy node)
    {
      //Contract.Requires(node != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      if (node.ProxyFor != null)
      {
        return base.VisitBvTypeProxy(node);
      }

      return Instantiate(node, new BvType(node.MinBits));
    }
  }
}