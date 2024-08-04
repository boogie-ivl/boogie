using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  /// <summary>
  /// A class representing a mathematical set.
  /// </summary>
  public class GSet<T> : ICloneable, IEnumerable, IEnumerable<T>
  {
    /*[Own]*/
    Dictionary<T, int> ht;
    List<T> arr; // keep elements in a well-defined order; otherwise iteration is non-deterministic

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(ht != null);
      Contract.Invariant(arr != null);
      Contract.Invariant(ht.Count == arr.Count);
    }


    public GSet()
    {
      ht = new Dictionary<T, int>();
      arr = new List<T>();
      //:base();
    }

    private GSet(Dictionary<T, int> /*!*/ ht, List<T> arr)
    {
      Contract.Requires(ht != null);
      Contract.Requires(arr != null);
      this.ht = ht;
      this.arr = arr;
      //:base();
    }

    public GSet(int capacity)
    {
      ht = new Dictionary<T, int>(capacity);
      arr = new List<T>(capacity);
      //:base();
    }


    public readonly static GSet<T> /*!*/
      Empty = new GSet<T>();

    public void Clear()
    {
      ht.Clear();
      arr.Clear();
    }

    /// <summary>
    /// This method idempotently adds "o" to the set.
    /// In notation:
    ///   this.SetElements =  this.SetElements_old \union {o};
    /// </summary>
    public void Add(T o)
    {
      if (!ht.ContainsKey(o))
      {
        ht[o] = arr.Count;
        arr.Add(o);
      }
    }

    /// <summary>
    /// this.SetElements =  this.SetElements_old \union s.GSet<T>Elements;
    /// </summary>
    public void AddRange(IEnumerable<T> s)
    {
      foreach (T o in s)
      {
        Add(o);
      }
    }

    /// <summary>
    /// this.SetElements =  this.SetElements_old \setminus {o};
    /// </summary>
    public void Remove(T o)
    {
      if (ht.TryGetValue(o, out var idx))
      {
        var last = arr[arr.Count - 1];
        arr.RemoveAt(arr.Count - 1);
        if (idx != arr.Count)
        {
          arr[idx] = last;
          ht[last] = idx;
        }

        ht.Remove(o);
      }
    }

    /// <summary>
    /// this.SetElements =  this.SetElements_old \setminus s.SetElements;
    /// </summary>
    public void RemoveRange(IEnumerable<T> s)
    {
      Contract.Requires(s != null);
      if (s == this)
      {
        ht.Clear();
        arr.Clear();
      }
      else
      {
        foreach (T o in s)
        {
          Remove(o);
        }
      }
    }

    /// <summary>
    /// Returns an arbitrary element from the set.
    /// </summary>
    public T Choose()
    {
      Contract.Requires((Count > 0));
      foreach (var e in this)
      {
        return e;
      }

      return default(T);
    }

    /// <summary>
    /// Picks an arbitrary element from the set, removes it, and returns it.
    /// </summary>
    public T Take()
    {
      Contract.Requires((Count > 0));
      Contract.Ensures(Count == Contract.OldValue(Count) - 1);
      T r = Choose();
      Remove(r);
      return r;
    }

    public void Intersect(GSet<T> /*!*/ s)
    {
      Contract.Requires(s != null);
      if (s == this)
      {
        return;
      }

      ht.Clear();
      var newArr = new List<T>();
      foreach (T key in arr)
      {
        if (s.ht.ContainsKey(key))
        {
          ht[key] = newArr.Count;
          newArr.Add(key);
        }
      }

      arr = newArr;
    }

    /// <summary>
    /// The getter returns true iff "o" is in the set.
    /// The setter adds the value "o" (for "true") or removes "o" (for "false")
    /// </summary>
    public bool this[T o]
    {
      get { return ht.ContainsKey(o); }
      set
      {
        if (value)
        {
          Add(o);
        }
        else
        {
          Remove(o);
        }
      }
    }

    /// <summary>
    /// Returns true iff "o" is an element of "this".
    /// </summary>
    /// <param name="o"></param>
    /// <returns></returns>
    [Pure]
    public bool Contains(T o)
    {
      return this.ht.ContainsKey(o);
    }

    /// <summary>
    /// Returns true iff every element of "s" is an element of "this", that is, if
    /// "s" is a subset of "this".
    /// </summary>
    /// <param name="s"></param>
    /// <returns></returns>
    public bool ContainsRange(IEnumerable<T> s)
    {
      Contract.Requires(s != null);
      if (s != this)
      {
        foreach (T key in s)
        {
          if (!this.ht.ContainsKey(key))
          {
            return false;
          }
        }
      }

      return true;
    }

    public object /*!*/ Clone()
    {
      Contract.Ensures(Contract.Result<object>() != null);
      return new GSet<T>(new Dictionary<T, int>(ht), new List<T>(arr));
    }

    public virtual int Count
    {
      get { return ht.Count; }
    }

    [Pure]
    public override string /*!*/ ToString()
    {
      Contract.Ensures(Contract.Result<string>() != null);
      string s = null;
      foreach (object /*!*/ key in ht.Keys)
      {
        Contract.Assert(key != null);
        if (s == null)
        {
          s = "{";
        }
        else
        {
          s += ", ";
        }

        s += key.ToString();
      }

      if (s == null)
      {
        return "{}";
      }
      else
      {
        return s + "}";
      }
    }

    //----------------------------- Static Methods ---------------------------------

    // Functional Intersect
    public static GSet<T> /*!*/ Intersect(GSet<T> /*!*/ a, GSet<T> /*!*/ b)
    {
      Contract.Requires(b != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<GSet<T>>() != null);
      //Contract.Ensures(Contract.ForAll(result, x => a[x] && b[x] ));
      GSet<T> /*!*/
        res = (GSet<T> /*!*/) Cce.NonNull(a.Clone());
      res.Intersect(b);
      return res;
    }

    // Functional Union
    public static GSet<T> /*!*/ Union(GSet<T> /*!*/ a, GSet<T> /*!*/ b)
    {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<GSet<T>>() != null);
      //  Contract.Ensures(Contract.ForAll(result, x => a[x] || b[x] ));
      GSet<T> /*!*/
        res = (GSet<T> /*!*/) Cce.NonNull(a.Clone());
      res.AddRange(b);
      return res;
    }

    public delegate bool SetFilter(object /*!*/ obj);

    public static GSet<T> /*!*/ Filter(GSet<T> /*!*/ a, Func<T, bool> filter)
    {
      Contract.Requires(filter != null);
      Contract.Requires(a != null);
      Contract.Ensures(Contract.Result<GSet<T>>() != null);
      GSet<T> inter = new GSet<T>();

      foreach (T elem in a)
      {
        Contract.Assert(elem != null);
        if (filter(elem))
        {
          inter.Add(elem);
        }
      }

      return inter;
    }

    public IEnumerator<T> GetEnumerator()
    {
      return arr.GetEnumerator();
    }

    IEnumerator IEnumerable.GetEnumerator()
    {
      return ((IEnumerable) arr).GetEnumerator();
    }

    public bool AddAll(IEnumerable s)
    {
      foreach (T e in s)
      {
        Add(e);
      }

      return true;
    }
  }


  public interface IWorkList : ICollection
  {
    bool Add(object o);
    bool AddAll(IEnumerable objs);
    bool IsEmpty();
    object Pull();
  }
}