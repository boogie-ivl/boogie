using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class FunctionCall : IAppliable
{
  public int ContentHash => 1;

  private IdentifierExpr /*!*/ name;

  public Function Func;

  public FunctionCall(IdentifierExpr name)
  {
    Contract.Requires(name != null);
    this.name = name;
  }

  public FunctionCall(Function f)
  {
    Contract.Requires(f != null);
    this.Func = f;
    this.name = new IdentifierExpr(Token.NoToken, f.Name);

    // We need set the type of this IdentifierExpr so ShallowType() works
    Debug.Assert(f.OutParams.Count > 0);
    this.name.Type = f.OutParams[0].TypedIdent.Type;
  }

  public string /*!*/ FunctionName
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.name.Name;
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(name != null);
  }

  public FunctionCall CreateUnresolvedCopy()
  {
    return new FunctionCall(new IdentifierExpr(name.tok, name.Name, name.Type));
  }

  [Pure]
  public override string ToString()
  {
    Contract.Ensures(Contract.Result<string>() != null);
    return name.Name;
  }

  [Pure]
  [Reads(ReadsAttribute.Reads.Nothing)]
  public override bool Equals(object other)
  {
    FunctionCall fc = other as FunctionCall;
    return fc != null && this.Func == fc.Func;
  }

  [Pure]
  public override int GetHashCode()
  {
    Contract.Assume(this.Func != null);
    return Func.GetHashCode();
  }

  public virtual void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
  {
    //Contract.Requires(stream != null);
    //Contract.Requires(args != null);

    if (stream.UseForComputingChecksums && Func.OriginalLambdaExprAsString != null)
    {
      stream.Write(Func.OriginalLambdaExprAsString);
    }
    else
    {
      this.name.Emit(stream, 0xF0, false);
    }

    if (stream.UseForComputingChecksums)
    {
      var c = Func.DependencyChecksum;
      if (c != null)
      {
        stream.Write(string.Format("[dependency_checksum:{0}]", c));
      }
    }

    stream.Write("(");
    args.Emit(stream);
    stream.Write(")");
  }

  public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
  {
    //Contract.Requires(subjectForErrorReporting != null);
    //Contract.Requires(rc != null);
    if (Func != null)
    {
      // already resolved
      return;
    }

    Func = rc.LookUpFunction(name.Name);
    if (Func == null)
    {
      rc.Error(this.name, "use of undeclared function: {0}", name.Name);
    }
    else if (name.Type == null)
    {
      // We need set the type of this IdentifierExpr so ShallowType() works
      Debug.Assert(name.Type == null);
      Debug.Assert(Func.OutParams.Count > 0);
      name.Type = Func.OutParams[0].TypedIdent.Type;
    }
  }

  public virtual int ArgumentCount
  {
    get
    {
      Contract.Assume(Func != null); // ArgumentCount requires object to be properly resolved.
      return Func.InParams.Count;
    }
  }

  public virtual Type Typecheck(IList<Expr> actuals, out TypeParamInstantiation tpInstantiation,
    TypecheckingContext tc)
  {
    //Contract.Requires(tc != null);
    //Contract.Requires(actuals != null);
    Contract.Ensures(Contract.ValueAtReturn(out actuals) != null);
    Contract.Ensures(Contract.ValueAtReturn(out tpInstantiation) != null);
    Contract.Assume(this.Func != null);
    Contract.Assume(actuals.Count == Func.InParams.Count);
    Contract.Assume(Func.OutParams.Count == 1);

    List<Type> actualResultType =
      Type.CheckArgumentTypes(Func.TypeParameters,
        out var resultingTypeArgs,
        Func.InParams.Select(Item => Item.TypedIdent.Type).ToList(),
        actuals,
        Func.OutParams.Select(Item => Item.TypedIdent.Type).ToList(),
        null,
        // we need some token to report a possibly wrong number of
        // arguments
        actuals.Count > 0 ? Cce.NonNull(actuals[0]).tok : Token.NoToken,
        "application of " + name.Name,
        tc);

    if (actualResultType == null)
    {
      tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
      return null;
    }
    else
    {
      Contract.Assert(actualResultType.Count == 1);
      tpInstantiation =
        SimpleTypeParamInstantiation.From(Func.TypeParameters, resultingTypeArgs);
      return actualResultType[0];
    }
  }

  public Type ShallowType(IList<Expr> args)
  {
    //Contract.Requires(args != null);
    Contract.Ensures(Contract.Result<Type>() != null);
    Contract.Assume(name.Type != null);
    return name.Type;
  }

  public virtual T Dispatch<T>(IAppliableVisitor<T> visitor)
  {
    //Contract.Requires(visitor != null);
    return visitor.Visit(this);
  }
}