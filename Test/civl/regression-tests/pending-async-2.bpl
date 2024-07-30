// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n > 0;

////////////////////////////////////////////////////////////////////////////////

async atomic action {:layer 1} A () {}
async atomic action {:layer 1} B () {}

left action {:layer 1} C ()
creates A;
{
  async call A();
  // create undeclared pending async to B
  async call B();
}

left action {:layer 1} D ()
creates A, B;
{
  // do nothing
}
