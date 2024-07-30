// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 1,2} SPEC ()
creates A;
{
  async call A(1);
}

yield procedure {:layer 1} b ()
refines SPEC;
{
  async call a(true, 1, 2.3); // This call is already to action A when it is turned into a pending async.
}

yield procedure {:layer 0} c ()
refines SPEC;
{
  async call a(true, 1, 2.3); // This call is still to procedure a when it is turned into a pending async.
}

async atomic action {:layer 1,2} A (i:int) { }

yield procedure {:layer 0} a ({:hide} b:bool, i:int, {:hide} r:real);
refines A;
