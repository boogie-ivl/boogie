using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
  public class LayerRange
  {
    public static int Min = 0;
    public static int Max = int.MaxValue;
    public static LayerRange MinMax = new LayerRange(Min, Max);

    public int LowerLayer;
    public int UpperLayer;

    public LayerRange(int layer) : this(layer, layer)
    {
    }

    public LayerRange(int lower, int upper)
    {
      Debug.Assert(lower <= upper);
      this.LowerLayer = lower;
      this.UpperLayer = upper;
    }

    public bool Contains(int layerNum)
    {
      return LowerLayer <= layerNum && layerNum <= UpperLayer;
    }

    public bool Subset(LayerRange other)
    {
      return other.LowerLayer <= LowerLayer && UpperLayer <= other.UpperLayer;
    }

    public bool OverlapsWith(LayerRange other)
    {
      return LowerLayer <= other.UpperLayer && other.LowerLayer <= UpperLayer;
    }

    public static LayerRange Union(LayerRange first, LayerRange second)
    {
      return new LayerRange(Math.Min(first.LowerLayer, second.LowerLayer), Math.Max(first.UpperLayer, second.UpperLayer));
    }

    public static LayerRange Union(List<LayerRange> layerRanges)
    {
      Debug.Assert(layerRanges.Any());
      var unionLayerRange = layerRanges.First();
      foreach (var layerRange in layerRanges)
      {
        unionLayerRange = Union(unionLayerRange, layerRange);
      }
      return unionLayerRange;
    }

    public override string ToString()
    {
      return $"[{LowerLayer}, {UpperLayer}]";
    }

    public override bool Equals(object obj)
    {
      LayerRange other = obj as LayerRange;
      if (obj == null)
      {
        return false;
      }

      return LowerLayer == other.LowerLayer && UpperLayer == other.UpperLayer;
    }

    public override int GetHashCode()
    {
      return (23 * 31 + LowerLayer) * 31 + UpperLayer;
    }
  }

  public static class CivlAttributes
  {
    public const string LAYER = "layer";
    public const string YIELDS = "yields";
    public const string MARK = "mark";
    public const string HIDE = "hide";
    public const string PENDING_ASYNC = "pending_async";
    public const string SYNC = "sync";
    public const string SKIP = "skip";
    public const string IS_RIGHT = "IS_right";
    public const string IS_LEFT = "IS_left";

    private static string[] CIVL_ATTRIBUTES = { LAYER, YIELDS, MARK, HIDE, PENDING_ASYNC, SYNC, IS_LEFT, IS_RIGHT };

    public const string LINEAR = "linear";
    public const string LINEAR_IN = "linear_in";
    public const string LINEAR_OUT = "linear_out";

    private static string[] LINEAR_ATTRIBUTES = { LINEAR, LINEAR_IN, LINEAR_OUT };

    public static bool HasCivlAttribute(this ICarriesAttributes obj)
    {
      for (var kv = obj.Attributes; kv != null; kv = kv.Next)
      {
        if (CIVL_ATTRIBUTES.Contains(kv.Key) || LINEAR_ATTRIBUTES.Contains(kv.Key))
        {
          return true;
        }
      }

      return false;
    }

    public static List<QKeyValue> FindAllAttributes(this ICarriesAttributes obj, string name)
    {
      var attributes = new List<QKeyValue>();
      for (var kv = obj.Attributes; kv != null; kv = kv.Next)
      {
        if (kv.Key == name)
        {
          attributes.Add(kv);
        }
      }

      return attributes;
    }

    public static bool HasAttribute(this ICarriesAttributes obj, string name)
    {
      return QKeyValue.FindBoolAttribute(obj.Attributes, name);
    }

    public static bool RemoveAttributes(ICarriesAttributes obj, Func<QKeyValue, bool> cond)
    {
      QKeyValue curr = obj.Attributes;
      bool removed = false;

      while (curr != null && cond(curr))
      {
        curr = curr.Next;
        removed = true;
      }

      obj.Attributes = curr;
      while (curr != null)
      {
        QKeyValue next = curr.Next;
        while (next != null && cond(next))
        {
          next = next.Next;
          removed = true;
        }

        curr.Next = next;
        curr = next;
      }

      return removed;
    }

    public static void RemoveAttributes(ICarriesAttributes obj, ICollection<string> keys)
    {
      RemoveAttributes(obj, kv => keys.Contains(kv.Key));
    }

    public static void RemoveCivlAttributes(ICarriesAttributes obj)
    {
      RemoveAttributes(obj, CIVL_ATTRIBUTES);
    }

    public static void RemoveLinearAttributes(ICarriesAttributes obj)
    {
      RemoveAttributes(obj, LINEAR_ATTRIBUTES);
    }

    public static bool IsCallMarked(CallCmd callCmd)
    {
      return callCmd.HasAttribute(MARK);
    }

    public static QKeyValue ApplySubstitutionToPoolHints(Substitution incarnationSubst, QKeyValue attributes)
    {
      if (attributes == null)
      {
        return null;
      }
      attributes = (QKeyValue)new Duplicator().Visit(attributes);
      var iter = attributes;
      while (iter != null)
      {
        if (iter.Key == "add_to_pool" && iter.Params.Count > 1)
        {
          var label = iter.Params[0] as string;
          if (label != null)
          {
            var newParams = new List<object> {label};
            for (int i = 1; i < iter.Params.Count; i++)
            {
              var instance = iter.Params[i] as Expr;
              if (instance != null)
              {
                instance = Substituter.Apply(incarnationSubst, instance);
                newParams.Add(instance);
              }
            }
            iter.ClearParams();
            iter.AddParams(newParams);
          }
        }
        iter = iter.Next;
      }
      return attributes;
    }
  }

  public static class CivlPrimitives
  {
    public static HashSet<string> LinearPrimitives = new()
    {
      "One_New", "One_To_Fractions", "Fractions_To_One",
      "Cell_Pack", "Cell_Unpack",
      "Map_MakeEmpty", "Map_Split", "Map_Get", "Map_Put", "Map_Assume",
      "Set_MakeEmpty", "Set_Split", "Set_Get", "Set_Put", "One_Split", "One_Get", "One_Put"
    };

    public static IdentifierExpr ExtractRootFromAccessPathExpr(Expr expr)
    {
      if (expr is IdentifierExpr identifierExpr)
      {
        return identifierExpr;
      }
      if (expr is NAryExpr nAryExpr)
      {
        if (nAryExpr.Fun is FieldAccess or MapSelect)
        {
          return ExtractRootFromAccessPathExpr(nAryExpr.Args[0]);
        }
      }
      return null;
    }

    public static IdentifierExpr ModifiedArgument(CallCmd callCmd)
    {
      switch (Monomorphizer.GetOriginalDecl(callCmd.Proc).Name)
      {
        case "One_New":
        case "Cell_Pack":
        case "Cell_Unpack":
        case "Set_MakeEmpty":
        case "Map_MakeEmpty":
        case "Map_Assume":
          return null;
        default:
          return ExtractRootFromAccessPathExpr(callCmd.Ins[0]);
      }
    }

    public static HashSet<string> Async = new()
    {
      "create_asyncs", "create_multi_asyncs", "set_choice"
    };
  }
}
