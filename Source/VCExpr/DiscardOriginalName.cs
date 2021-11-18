using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  public class DiscardOriginalName : ScopedNamer
  {
    private const string controlFlow = "ControlFlow"; // This is a hardcoded name used by Boogie to inspect the SMT model.

    private readonly Dictionary<string, string> globalNewToOldName = new ();

    public DiscardOriginalName() : base()
    {
    }

    private DiscardOriginalName(DiscardOriginalName namer) : base(namer)
    {
      globalNewToOldName = new(namer.globalNewToOldName);
    }

    public override void Reset()
    {
      base.Reset();
      globalNewToOldName.Clear();
    }

    public override string GetName(Object thingie, string inherentName)
    {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = this[thingie];
      if (res != null)
      {
        return res;
      }

      var uniqueInherentName = NextFreeName(thingie, inherentName);
      res = uniqueInherentName == controlFlow ? uniqueInherentName : NextFreeName(thingie, "$generated");
      
      GlobalNames.Add(thingie, res);
      globalNewToOldName.Add(res, uniqueInherentName);

      return res;
    }

    public override string GetLocalName(Object thingie, string inherentName)
    {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (inherentName != controlFlow) {
        inherentName = "n";
      }

      string res = NextFreeName(thingie, inherentName);
      LocalNames[^1][thingie] = res;
      return res;
    }

    public override string GetOriginalName(string newName)
    {
      return globalNewToOldName.GetValueOrDefault(newName, newName);
    }
    
    public override UniqueNamer Clone()
    {
      return new DiscardOriginalName(this);
    }
  }
}