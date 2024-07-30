using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public sealed class Block : Absy
{
  private string /*!*/ label; // Note, Label is mostly readonly, but it can change to the name of a nearby block during block coalescing and empty-block removal

  public string /*!*/ Label
  {
    get
    {
      Contract.Ensures(Contract.Result<string>() != null);
      return this.label;
    }
    set
    {
      Contract.Requires(value != null);
      this.label = value;
    }
  }

  [Rep] [ElementsPeer] public List<Cmd> /*!*/ cmds;

  public List<Cmd> /*!*/ Cmds
  {
    get
    {
      Contract.Ensures(Contract.Result<List<Cmd>>() != null);
      return this.cmds;
    }
    set
    {
      Contract.Requires(value != null);
      this.cmds = value;
    }
  }

  public IEnumerable<Block> Exits()
  {
    if (TransferCmd is GotoCmd g)
    {
      return cce.NonNull(g.labelTargets);
    }
    return new List<Block>();
  }

  [Rep] //PM: needed to verify Traverse.Visit
  public TransferCmd
    TransferCmd; // maybe null only because we allow deferred initialization (necessary for cyclic structures)

  public byte[] Checksum;

  // Abstract interpretation

  // public bool currentlyTraversed;

  public enum VisitState
  {
    ToVisit,
    BeingVisited,
    AlreadyVisited
  } // used by WidenPoints.Compute

  public VisitState TraversingStatus;

  public int aiId; // block ID used by the abstract interpreter, which may change these numbers with each AI run
  public bool widenBlock;

  public int
    iterations; // Count the number of time we visited the block during fixpoint computation. Used to decide if we widen or not

  // VC generation and SCC computation
  public List<Block> /*!*/ Predecessors;

  // This field is used during passification to null-out entries in block2Incarnation dictionary early
  public int succCount;

  private HashSet<Variable /*!*/> _liveVarsBefore;

  public IEnumerable<Variable /*!*/> liveVarsBefore
  {
    get
    {
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Variable /*!*/>>(), true));
      if (this._liveVarsBefore == null)
      {
        return null;
      }
      else
      {
        return this._liveVarsBefore.AsEnumerable<Variable>();
      }
    }
    set
    {
      Contract.Requires(cce.NonNullElements(value, true));
      if (value == null)
      {
        this._liveVarsBefore = null;
      }
      else
      {
        this._liveVarsBefore = new HashSet<Variable>(value);
      }
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(this.label != null);
    Contract.Invariant(this.cmds != null);
    Contract.Invariant(cce.NonNullElements(this._liveVarsBefore, true));
  }

  public bool IsLive(Variable v)
  {
    Contract.Requires(v != null);
    if (liveVarsBefore == null)
    {
      return true;
    }

    return liveVarsBefore.Contains(v);
  }

  public Block()
    : this(Token.NoToken, "", new List<Cmd>(), new ReturnCmd(Token.NoToken))
  {
  }

  public Block(IToken tok, string /*!*/ label, List<Cmd> /*!*/ cmds, TransferCmd transferCmd)
    : base(tok)
  {
    Contract.Requires(label != null);
    Contract.Requires(cmds != null);
    Contract.Requires(tok != null);
    this.label = label;
    this.cmds = cmds;
    this.TransferCmd = transferCmd;
    this.Predecessors = new List<Block>();
    this._liveVarsBefore = null;
    this.TraversingStatus = VisitState.ToVisit;
    this.iterations = 0;
  }

  public void Emit(TokenTextWriter stream, int level)
  {
    Contract.Requires(stream != null);
    stream.WriteLine();
    stream.WriteLine(
      this,
      level,
      "{0}:{1}",
      stream.Options.PrintWithUniqueASTIds
        ? String.Format("h{0}^^{1}", this.GetHashCode(), this.Label)
        : this.Label,
      this.widenBlock ? "  // cut point" : "");

    foreach (Cmd /*!*/ c in this.Cmds)
    {
      Contract.Assert(c != null);
      c.Emit(stream, level + 1);
    }

    Contract.Assume(this.TransferCmd != null);
    this.TransferCmd.Emit(stream, level + 1);
  }

  public void Register(ResolutionContext rc)
  {
    Contract.Requires(rc != null);
    rc.AddBlock(this);
  }

  public override void Resolve(ResolutionContext rc)
  {
    foreach (Cmd /*!*/ c in Cmds)
    {
      Contract.Assert(c != null);
      c.Resolve(rc);
    }

    Contract.Assume(this.TransferCmd != null);
    TransferCmd.Resolve(rc);
  }

  public override void Typecheck(TypecheckingContext tc)
  {
    foreach (Cmd /*!*/ c in Cmds)
    {
      Contract.Assert(c != null);
      c.Typecheck(tc);
    }

    Contract.Assume(this.TransferCmd != null);
    TransferCmd.Typecheck(tc);
  }

  /// <summary>
  /// Reset the abstract intepretation state of this block. It does this by putting the iterations to 0 and the pre and post states to null
  /// </summary>
  public void ResetAbstractInterpretationState()
  {
    //      this.currentlyTraversed = false;
    this.TraversingStatus = VisitState.ToVisit;
    this.iterations = 0;
  }

  [Pure]
  public override string ToString()
  {
    Contract.Ensures(Contract.Result<string>() != null);
    return this.Label + (this.widenBlock ? "[w]" : "");
  }

  public override Absy StdDispatch(StandardVisitor visitor)
  {
    Contract.Ensures(Contract.Result<Absy>() != null);
    return visitor.VisitBlock(this);
  }
}