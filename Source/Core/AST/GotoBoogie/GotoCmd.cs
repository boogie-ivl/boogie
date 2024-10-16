using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class GotoCmd : TransferCmd
{
  [Rep] public List<String> LabelNames;
  [Rep] public List<Block> LabelTargets;

  public QKeyValue Attributes { get; set; }
    
  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(LabelNames == null || LabelTargets == null || LabelNames.Count == LabelTargets.Count);
  }

  [NotDelayed]
  public GotoCmd(IToken /*!*/ tok, List<String> /*!*/ labelSeq)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(labelSeq != null);
    this.LabelNames = labelSeq;
  }

  public GotoCmd(IToken /*!*/ tok, List<String> /*!*/ labelSeq, List<Block> /*!*/ blockSeq)
    : base(tok)
  {
    Contract.Requires(tok != null);
    Contract.Requires(labelSeq != null);
    Contract.Requires(blockSeq != null);
    Debug.Assert(labelSeq.Count == blockSeq.Count);
    for (int i = 0; i < labelSeq.Count; i++)
    {
      Debug.Assert(Equals(labelSeq[i], cce.NonNull(blockSeq[i]).Label));
    }

    this.LabelNames = labelSeq;
    this.LabelTargets = blockSeq;
  }

  public GotoCmd(IToken /*!*/ tok, List<Block> /*!*/ blockSeq)
    : base(tok)
  {
    //requires (blockSeq[i] != null ==> blockSeq[i].Label != null);
    Contract.Requires(tok != null);
    Contract.Requires(blockSeq != null);
    List<String> labelSeq = new List<String>();
    for (int i = 0; i < blockSeq.Count; i++)
    {
      labelSeq.Add(cce.NonNull(blockSeq[i]).Label);
    }

    this.LabelNames = labelSeq;
    this.LabelTargets = blockSeq;
  }

  public void RemoveTarget(Block b) {
    LabelNames.Remove(b.Label);
    LabelTargets.Remove(b);
  }
    
  public void AddTarget(Block b)
  {
    Contract.Requires(b != null);
    Contract.Requires(b.Label != null);
    Contract.Requires(this.LabelTargets != null);
    Contract.Requires(this.LabelNames != null);
    this.LabelTargets.Add(b);
    this.LabelNames.Add(b.Label);
  }

  public void AddTargets(IEnumerable<Block> blocks)
  {
    Contract.Requires(blocks != null);
    Contract.Requires(cce.NonNullElements(blocks));
    Contract.Requires(this.LabelTargets != null);
    Contract.Requires(this.LabelNames != null);
    foreach (var block in blocks)
    {
      AddTarget(block);
    }
  }

  public override void Emit(TokenTextWriter stream, int level)
  {
    //Contract.Requires(stream != null);
    Contract.Assume(this.LabelNames != null);
    stream.Write(this, level, "goto ");
    if (stream.Options.PrintWithUniqueASTIds)
    {
      if (LabelTargets == null)
      {
        string sep = "";
        foreach (string name in LabelNames)
        {
          stream.Write("{0}{1}^^{2}", sep, "NoDecl", name);
          sep = ", ";
        }
      }
      else
      {
        string sep = "";
        foreach (Block /*!*/ b in LabelTargets)
        {
          Contract.Assert(b != null);
          stream.Write("{0}h{1}^^{2}", sep, b.GetHashCode(), b.Label);
          sep = ", ";
        }
      }
    }
    else
    {
      LabelNames.Emit(stream);
    }

    stream.WriteLine(";");
  }

  public override void Resolve(ResolutionContext rc)
  {
    //Contract.Requires(rc != null);
    Contract.Ensures(LabelTargets != null);
    if (LabelTargets != null)
    {
      // already resolved
      return;
    }

    Contract.Assume(this.LabelNames != null);
    LabelTargets = new List<Block>();
    foreach (string /*!*/ lbl in LabelNames)
    {
      Contract.Assert(lbl != null);
      Block b = rc.LookUpBlock(lbl);
      if (b == null)
      {
        rc.Error(this, "goto to unknown block: {0}", lbl);
      }
      else
      {
        LabelTargets.Add(b);
      }
    }

    Debug.Assert(rc.ErrorCount > 0 || LabelTargets.Count == LabelNames.Count);
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    //Contract.Requires(visitor != null);
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitGotoCmd(this);
  }
}