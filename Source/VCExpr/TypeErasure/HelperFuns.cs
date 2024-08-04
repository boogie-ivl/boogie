using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.TypeErasure;

public class HelperFuns
{
  public static Function BoogieFunction(string name, List<TypeVariable /*!*/> /*!*/ typeParams, params Type[] types)
  {
    Contract.Requires(types != null);
    Contract.Requires(name != null);
    Contract.Requires(Cce.NonNullElements(typeParams));
    Contract.Requires(types.Length > 0);
    Contract.Requires(Contract.ForAll(0, types.Length, i => types[i] != null));
    Contract.Ensures(Contract.Result<Function>() != null);

    List<Variable> args = new List<Variable>();
    for (int i = 0; i < types.Length - 1; ++i)
    {
      args.Add(new Formal(Token.NoToken,
        new TypedIdent(Token.NoToken, "arg" + i, Cce.NonNull(types[i])),
        true));
    }

    Formal result = new Formal(Token.NoToken,
      new TypedIdent(Token.NoToken, "res",
        Cce.NonNull(types)[types.Length - 1]),
      false);
    return new Function(Token.NoToken, name, new List<TypeVariable>(typeParams), args, result);
  }

  public static Function BoogieFunction(string name, params Type[] types)
  {
    Contract.Requires(types != null);
    Contract.Requires(name != null);
    Contract.Ensures(Contract.Result<Function>() != null);
    return BoogieFunction(name, new List<TypeVariable /*!*/>(), types);
  }

  // boogie function where all arguments and the result have the same type U
  public static Function UniformBoogieFunction(string name, int arity, Type U)
  {
    Contract.Requires(U != null);
    Contract.Requires(name != null);
    Contract.Ensures(Contract.Result<Function>() != null);
    Type[] /*!*/
      types = new Type[arity + 1];
    for (int i = 0; i < arity + 1; ++i)
    {
      types[i] = U;
    }

    return BoogieFunction(name, types);
  }

  public static List<VCExprVar /*!*/> /*!*/ GenVarsForInParams(Function fun, VCExpressionGenerator gen)
  {
    Contract.Requires(gen != null);
    Contract.Requires(fun != null);
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
    List<VCExprVar /*!*/> /*!*/
      arguments = new List<VCExprVar /*!*/>(fun.InParams.Count);
    foreach (Formal /*!*/ f in fun.InParams)
    {
      Contract.Assert(f != null);
      VCExprVar /*!*/
        var = gen.Variable(f.Name, f.TypedIdent.Type);
      arguments.Add(var);
    }

    return arguments;
  }

  public static List<T /*!*/> /*!*/ ToList<T>(params T[] args) where T : class
  {
    Contract.Requires(Cce.NonNullElements(args));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<T>>()));
    return new List<T>(args);
  }

  public static List<VCExpr /*!*/> /*!*/ ToVCExprList(List<VCExprVar /*!*/> /*!*/ list)
  {
    Contract.Requires(Cce.NonNullElements(list));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExpr>>()));
    return new List<VCExpr>(list);
  }

  public static List<VCExprVar /*!*/> /*!*/ VarVector(string baseName, int num, Type type, VCExpressionGenerator gen)
  {
    Contract.Requires(gen != null);
    Contract.Requires(type != null);
    Contract.Requires(baseName != null);
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
    List<VCExprVar /*!*/> /*!*/
      res = new List<VCExprVar /*!*/>(num);
    for (int i = 0; i < num; ++i)
    {
      res.Add(gen.Variable(baseName + i, type));
    }

    return res;
  }

  public static List<VCExprVar /*!*/> /*!*/
    VarVector(string baseName, List<Type /*!*/> /*!*/ types, VCExpressionGenerator gen)
  {
    Contract.Requires(gen != null);
    Contract.Requires(baseName != null);
    Contract.Requires(Cce.NonNullElements(types));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<List<VCExprVar>>()));
    List<VCExprVar /*!*/> /*!*/
      res = new List<VCExprVar /*!*/>(types.Count);
    for (int i = 0; i < types.Count; ++i)
    {
      res.Add(gen.Variable(baseName + i, types[i]));
    }

    return res;
  }
}