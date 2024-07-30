#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using Microsoft.Boogie;

namespace VCGeneration.Prune;

record RevealedState(HideRevealCmd.Modes Mode, IImmutableSet<Function> Offset) {
  public bool IsRevealed(Function function) {
    return (Mode == HideRevealCmd.Modes.Hide) == Offset.Contains(function);
  }

  public static readonly RevealedState AllRevealed = new(HideRevealCmd.Modes.Reveal, ImmutableHashSet<Function>.Empty);
  public static readonly RevealedState AllHidden = new(HideRevealCmd.Modes.Hide, ImmutableHashSet<Function>.Empty);
}

class RevealedAnalysis : DataflowAnalysis<Absy, ImmutableStack<RevealedState>> {
  
  public RevealedAnalysis(IReadOnlyList<Absy> roots, 
    Func<Absy, IEnumerable<Absy>> getNext, 
    Func<Absy, IEnumerable<Absy>> getPrevious) : base(roots, getNext, getPrevious)
  {
  }

  protected override ImmutableStack<RevealedState> Empty => ImmutableStack<RevealedState>.Empty.Push(
    RevealedState.AllRevealed);

  protected override ImmutableStack<RevealedState> Merge(ImmutableStack<RevealedState> first, ImmutableStack<RevealedState> second) {
    if (first.IsEmpty && second.IsEmpty) {
      return ImmutableStack<RevealedState>.Empty;
    }
    var firstElement = first.Peek();
    var secondElement = second.Peek();
    var mergedTop = MergeStates(firstElement, secondElement);
    var mergedTail = Merge(first.Pop(), second.Pop());
    return mergedTail.Push(mergedTop);
  }

  protected override bool StateEquals(ImmutableStack<RevealedState> first, ImmutableStack<RevealedState> second) {
    return first.Peek().Equals(second.Peek());
  }

  /// <summary>
  /// Takes the union of what is revealed.
  /// </summary>
  public static RevealedState MergeStates(RevealedState first, RevealedState second) {
    if (first.Mode == HideRevealCmd.Modes.Reveal && second.Mode == HideRevealCmd.Modes.Reveal) {
      var intersect = first.Offset.Intersect(second.Offset);
      if (intersect.Count == first.Offset.Count) {
        return first;
      }
      return new RevealedState(HideRevealCmd.Modes.Reveal, intersect);
    }

    if (first.Mode == HideRevealCmd.Modes.Reveal) {
      return first;
    }
    
    if (second.Mode == HideRevealCmd.Modes.Reveal) {
      return second;
    }

    var union = first.Offset.Union(second.Offset);
    if (union.Count == first.Offset.Count) {
      return first;
    }
    return new RevealedState(HideRevealCmd.Modes.Hide, union);
  }

  static RevealedState GetUpdatedState(HideRevealCmd hideRevealCmd, RevealedState state) {
    if (hideRevealCmd.Function == null) {
      return new RevealedState(hideRevealCmd.Mode, ImmutableHashSet<Function>.Empty);
    }

    var newOffset = hideRevealCmd.Mode == state.Mode
      ? state.Offset.Remove(hideRevealCmd.Function)
      : state.Offset.Add(hideRevealCmd.Function);
    return state with { Offset = newOffset };
  }
  
  protected override ImmutableStack<RevealedState> Update(Absy node, ImmutableStack<RevealedState> state) {
    if (state.IsEmpty) {
      throw new Exception("Unbalanced use of push and pop commands");
    }

    if (node is ChangeScope changeScope) {
      return changeScope.Mode == ChangeScope.Modes.Push ? state.Push(state.Peek()) : state.Pop();
    }

    if (node is HideRevealCmd hideRevealCmd) {
      var latestState = state.Peek();
      var updatedState = GetUpdatedState(hideRevealCmd, latestState);
      return updatedState.Equals(latestState) ? state : state.Pop().Push(updatedState);
    }

    return state;
  }
}