// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:[int]int;

yield invariant {:layer 1} yield_x({:linear} tid: One int);
invariant x[tid->val] == 0;

async atomic action {:layer 1} A ({:linear} tid: One int)
modifies x;
{
  x[tid->val] := 1;
}

left action {:layer 1} ASYNC_A ({:linear_in} tid: One int)
 creates A;
{
  async call A(tid);
}

yield procedure {:layer 1} dummy () {}
