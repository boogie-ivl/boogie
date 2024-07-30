// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

async atomic action {:layer 1} A ()
modifies x;
{
  x := x - 1;
}

left action {:layer 1} ASYNC_A ()
creates A;
{
  async call A();
}

yield procedure {:layer 1} dummy () {}
