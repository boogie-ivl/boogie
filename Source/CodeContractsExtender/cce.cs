using System;
using SA = System.Attribute;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

/// <summary>
/// A class containing static methods to extend the functionality of Code Contracts
/// </summary>
public static class Cce
{
  //[Pure]
  //public static bool NonNullElements<T>(Microsoft.Dafny.Graph<T> collection) {
  //  return collection != null && cce.NonNullElements(collection.TopologicallySortedComponents());
  //}
  [Pure]
  public static T NonNull<T>(T t) where T : class
  {
    Contract.Requires(t != null);
    Contract.Ensures(Contract.Result<T>() != null);
    return t;
  }

  [Pure]
  public static bool NonNullElements<T>(IEnumerable<T> collection) where T : class
  {
    return collection != null && Contract.ForAll(collection, c => c != null);
  }

  [Pure]
  public static bool NonNullDictionaryAndValues<TKey, TValue>(IDictionary<TKey, TValue> collection) where TValue : class
  {
    return collection != null && Cce.NonNullElements(collection.Values);
  }

  //[Pure]
  //public static bool NonNullElements(List<Variable> collection) {
  //  return collection != null && Contract.ForAll(0, collection.Length, i => collection[i] != null);
  //}
  /// <summary>
  /// For possibly-null lists of non-null elements
  /// </summary>
  /// <typeparam name="T"></typeparam>
  /// <param name="collection"></param>
  /// <param name="nullability">If true, the collection is treated as an IEnumerable&lt;T!&gt;?, rather than an IEnumerable&lt;T!&gt;!</param>
  /// <returns></returns>
  [Pure]
  public static bool NonNullElements<T>(IEnumerable<T> collection, bool nullability) where T : class
  {
    return (nullability && collection == null) || Cce.NonNullElements(collection);
    //Should be the same as:
    /*if(nullability&&collection==null)
     * return true;
     * return cce.NonNullElements(collection)
     */
  }

  [Pure]
  public static bool NonNullElements<TKey, TValue>(KeyValuePair<TKey, TValue> kvp)
    where TKey : class where TValue : class
  {
    return kvp.Key != null && kvp.Value != null;
  }

  [Pure]
  public static bool NonNullElements<T>(IEnumerator<T> iEnumerator) where T : class
  {
    return iEnumerator != null;
  }

  [Pure]
  public static bool NonNull<T>(HashSet<T> set) where T : class
  {
    return set != null && !set.Contains(null);
  }

  //[Pure]
  //public static bool NonNullElements<T>(Graphing.Graph<T> graph) {
  //  return cce.NonNullElements(graph.TopologicalSort());
  //}
  [Pure]
  public static void BeginExpose(object o)
  {
  }

  [Pure]
  public static void EndExpose()
  {
  }

  [Pure]
  public static bool IsPeerConsistent(object o)
  {
    return true;
  }

  [Pure]
  public static bool IsConsistent(object o)
  {
    return true;
  }

  [Pure]
  public static bool IsExposable(object o)
  {
    return true;
  }

  [Pure]
  public static bool IsExposed(object o)
  {
    return true;
  }

  [Pure]
  public static bool IsNew(object o)
  {
    return true;
  }

  public static class Owner
  {
    [Pure]
    public static bool Same(object o, object p)
    {
      return true;
    }

    [Pure]
    public static void AssignSame(object o, object p)
    {
    }

    [Pure]
    public static object ElementProxy(object o)
    {
      return o;
    }

    [Pure]
    public static bool None(object o)
    {
      return true;
    }

    [Pure]
    public static bool Different(object o, object p)
    {
      return true;
    }

    [Pure]
    public static bool New(object o)
    {
      return true;
    }
  }

  [Pure]
  public static void LoopInvariant(bool p)
  {
    Contract.Assert(p);
  }

  public class UnreachableException : Exception
  {
    public UnreachableException()
    {
    }
  }
}

public class PeerAttribute : SA
{
}

public class RepAttribute : SA
{
}

public class CapturedAttribute : SA
{
}

public class NotDelayedAttribute : SA
{
}

public class NoDefaultContractAttribute : SA
{
}

public class VerifyAttribute : SA
{
  public VerifyAttribute(bool b)
  {
  }
}

public class StrictReadonlyAttribute : SA
{
}

public class AdditiveAttribute : SA
{
}

public class ReadsAttribute : SA
{
  public enum Reads
  {
    Nothing,
    Everything,
  }

  public ReadsAttribute(object o)
  {
  }
}

public class GlobalAccessAttribute : SA
{
  public GlobalAccessAttribute(bool b)
  {
  }
}

public class EscapesAttribute : SA
{
  public EscapesAttribute(bool b, bool b_2)
  {
  }
}

public class NeedsContractsAttribute : SA
{
  public NeedsContractsAttribute()
  {
  }

  public NeedsContractsAttribute(bool ret, bool parameters)
  {
  }

  public NeedsContractsAttribute(bool ret, int[] parameters)
  {
  }
}

public class ImmutableAttribute : SA
{
}

public class InsideAttribute : SA
{
}

public class SpecPublicAttribute : SA
{
}

public class ElementsPeerAttribute : SA
{
}

public class ResultNotNewlyAllocatedAttribute : SA
{
}

public class OnceAttribute : SA
{
}