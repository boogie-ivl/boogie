using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  /**
   * Visitor that establishes unique variable (or constant) names in a VCExpr.
   * This is done by adding a counter as suffix if name clashes occur
   * TODO: also handle type variables here
   */
  public abstract class ScopedNamer : UniqueNamer
  {
    private static ISet<string> boogieDeterminedNames = new HashSet<string>() { };

    public static void AddBoogieDeterminedName(string name) {
      boogieDeterminedNames.Add(name);
    }
      
    public string Spacer = "@@";
    protected IDictionary<Object /*!*/, string /*!*/> /*!*/ GlobalNames;

    protected List<IDictionary<Object /*!*/, string /*!*/> /*!*/> /*!*/ LocalNames;

    protected HashSet<string /*!*/> /*!*/ UsedNames;

    protected IDictionary<string /*!*/, int /*!*/> /*!*/ CurrentCounters;

    protected IDictionary<Object /*!*/, string /*!*/> /*!*/ GlobalPlusLocalNames;
    protected Dictionary<string, string> globalNewToOldName = new ();

    protected ScopedNamer()
    {
      GlobalNames = new Dictionary<Object, string>();
      LocalNames = new() { new Dictionary<object, string>() };
      UsedNames = new HashSet<string>();
      CurrentCounters = new Dictionary<string, int>();
      GlobalPlusLocalNames = new Dictionary<Object, string>();
    }
    
    protected ScopedNamer(ScopedNamer namer)
    {
      Contract.Requires(namer != null);

      Spacer = namer.Spacer;
      GlobalNames = new Dictionary<Object, string>(namer.GlobalNames);
      LocalNames = new List<IDictionary<Object, string>>();

      foreach (IDictionary<Object /*!*/, string /*!*/> /*!*/ d in namer.LocalNames)
      {
        LocalNames.Add(new Dictionary<Object /*!*/, string /*!*/>(d));
      }

      UsedNames = new HashSet<string>(namer.UsedNames);
      CurrentCounters = new Dictionary<string, int>(namer.CurrentCounters);
      GlobalPlusLocalNames = new Dictionary<Object, string>(namer.GlobalPlusLocalNames);
      globalNewToOldName = new(namer.globalNewToOldName);
    }

    [ContractInvariantMethod]
    private void GlobalNamesInvariantMethod()
    {
      Contract.Invariant(Cce.NonNullDictionaryAndValues(GlobalNames));
    }

    [ContractInvariantMethod]
    private void LocalNamesInvariantMethod()
    {
      Contract.Invariant(Contract.ForAll(LocalNames, i => i != null && Cce.NonNullDictionaryAndValues(i)));
    }

    [ContractInvariantMethod]
    private void UsedNamesInvariantMethod()
    {
      Contract.Invariant(Cce.NonNull(UsedNames));
    }

    [ContractInvariantMethod]
    private void CurrentCountersInvariantMethod()
    {
      Contract.Invariant(CurrentCounters != null);
    }

    [ContractInvariantMethod]
    private void GlobalPlusLocalNamesInvariantMethod()
    {
      Contract.Invariant(Cce.NonNullDictionaryAndValues(GlobalPlusLocalNames));
    }

    public void PushScope()
    {
      LocalNames.Add(new Dictionary<Object /*!*/, string /*!*/>());
    }

    public abstract UniqueNamer Clone();

    public void PopScope()
    {
      LocalNames.RemoveAt(LocalNames.Count - 1);
    }

    protected string NextFreeName(Object thing, string baseName)
    {
      Contract.Requires(baseName != null);
      Contract.Requires(thing != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string /*!*/ candidate;

      if (CurrentCounters.TryGetValue(baseName, out var counter))
      {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      }
      else
      {
        candidate = baseName;
        counter = 0;
      }

      while (UsedNames.Contains(candidate))
      {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      }

      UsedNames.Add(candidate);
      CurrentCounters[baseName] = counter;
      GlobalPlusLocalNames[thing] = candidate;
      return candidate;
    }

    [Pure]
    public string this[Object /*!*/ thingie]
    {
      get
      {
        Contract.Requires(thingie != null);

        string res;
        for (int i = LocalNames.Count - 1; i >= 0; --i)
        {
          if (LocalNames[i].TryGetValue(thingie, out res))
          {
            return res;
          }
        }

        GlobalNames.TryGetValue(thingie, out res);
        return res;
      }
    }

    public string Lookup(Object thingie)
    {
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (GlobalPlusLocalNames.TryGetValue(thingie, out var name))
      {
        return name;
      }

      return Spacer + "undefined" + Spacer + thingie.GetHashCode() + Spacer;
    }

    public virtual string GetName(object thing, string inherentName)
    {
      Contract.Requires(inherentName != null);
      Contract.Requires(thing != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string result = this[thing];
      if (result != null)
      {
        return result;
      }

      var uniqueInherentName = NextFreeName(thing, inherentName);
      if (thing is NamedDeclaration namedDeclaration && !namedDeclaration.MayRename)
      {
        result = uniqueInherentName;
      }
      else if (boogieDeterminedNames.Contains(inherentName))
      {
        result = uniqueInherentName;
      }
      else {
        var modifiedName = GetModifiedName(uniqueInherentName);
        if (modifiedName != uniqueInherentName) {
          result = NextFreeName(thing, modifiedName);
          globalNewToOldName.Add(result, uniqueInherentName);
        } 
        else
        {
          result = uniqueInherentName;
        }
      }

      GlobalNames.Add(thing, result);

      return result;
    }

    protected abstract string GetModifiedName(string uniqueInherentName);

    public virtual string GetLocalName(Object thing, string inherentName)
    {
      Contract.Requires(inherentName != null);
      Contract.Requires(thing != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (!boogieDeterminedNames.Contains(inherentName)) {
        inherentName = GetModifiedName(inherentName);
      }

      string res = NextFreeName(thing, inherentName);
      LocalNames[^1][thing] = res;
      return res;
    }

    public virtual string GetOriginalName(string newName)
    {
      return globalNewToOldName.GetValueOrDefault(newName, newName);
    }
  }
}