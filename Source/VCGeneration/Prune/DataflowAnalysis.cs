using System;
using System.Collections.Generic;
using System.Linq;

namespace VCGeneration.Prune;

/// <summary>
/// Allows defining dataflow analysis
/// </summary>
abstract class DataflowAnalysis<TNode, TState> {
  protected readonly Dictionary<TNode, TState> outStates = new();
  protected readonly Dictionary<TNode, TState> inStates = new();
  private readonly Func<TNode, IEnumerable<TNode>> getNext;
  private readonly Func<TNode, IEnumerable<TNode>> getPrevious;
  private readonly IReadOnlyList<TNode> roots;

  protected DataflowAnalysis(IReadOnlyList<TNode> roots,  
    Func<TNode, IEnumerable<TNode>> getNext,
    Func<TNode, IEnumerable<TNode>> getPrevious) {
    this.getNext = getNext;
    this.getPrevious = getPrevious;
    this.roots = roots;
  }

  public IReadOnlyDictionary<TNode, TState> States => outStates;
  
  protected abstract TState Empty { get; }

  protected abstract TState Merge(TState first, TState second);

  protected abstract bool StateEquals(TState first, TState second);
  
  protected abstract TState Update(TNode node, TState state);

  public void Run() {
    var stack = new Stack<TNode>();
    foreach (var node in roots) {
      stack.Push(node);
    }
    while (stack.Any()) {
      var node = stack.Pop();
      var previous = getPrevious(node);
      var previousStates = previous.Select(p => outStates.GetValueOrDefault(p)).Where(x => x != null).ToList();
      var inState = previousStates.Any() ? previousStates.Aggregate(Merge) : Empty;
      if (inStates.ContainsKey(node) && StateEquals(inState, inStates[node])) {
        continue;
      }

      inStates[node] = inState;
      var outState = Update(node, inState);
      var previousOutState = outStates.GetValueOrDefault(node);
      if (previousOutState == null || !StateEquals(outState, previousOutState)) {
        outStates[node] = outState;
        foreach (var next in getNext(node)) {
          stack.Push(next);
        }
      }
    }
  }
}