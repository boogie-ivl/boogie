﻿using System;
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

    public int lowerLayerNum;
    public int upperLayerNum;

    public LayerRange(int layer) : this(layer, layer)
    {
    }

    public LayerRange(int lower, int upper)
    {
      Debug.Assert(lower <= upper);
      this.lowerLayerNum = lower;
      this.upperLayerNum = upper;
    }

    public bool Contains(int layerNum)
    {
      return lowerLayerNum <= layerNum && layerNum <= upperLayerNum;
    }

    public bool Subset(LayerRange other)
    {
      return other.lowerLayerNum <= lowerLayerNum && upperLayerNum <= other.upperLayerNum;
    }

    public bool OverlapsWith(LayerRange other)
    {
      return lowerLayerNum <= other.upperLayerNum && other.lowerLayerNum <= upperLayerNum;
    }

    public override string ToString()
    {
      return $"[{lowerLayerNum}, {upperLayerNum}]";
    }

    public override bool Equals(object obj)
    {
      LayerRange other = obj as LayerRange;
      if (obj == null)
      {
        return false;
      }

      return lowerLayerNum == other.lowerLayerNum && upperLayerNum == other.upperLayerNum;
    }

    public override int GetHashCode()
    {
      return (23 * 31 + lowerLayerNum) * 31 + upperLayerNum;
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

    private static string[] CIVL_ATTRIBUTES = { LAYER, YIELDS, MARK, HIDE, PENDING_ASYNC, SYNC };

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
  }

  public static class CivlPrimitives
  {
    public static HashSet<string> Linear = new()
    {
      "Lheap_Empty", "Lheap_Split", "Lheap_Transfer", "Lheap_Read", "Lheap_Write", "Lheap_Add", "Lheap_Remove",
      "Lset_Empty", "Lset_Split", "Lset_Transfer",
      "Lval_Split", "Lval_Transfer"
    };

    public static HashSet<string> Async = new()
    {
      "create_async", "create_asyncs", "create_multi_asyncs", "set_choice"
    };
  }
}