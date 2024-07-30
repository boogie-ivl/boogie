// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x:int;

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 1} MAIN ()
refines MAIN';
creates INC, DEC;
{
  async call INC();
  async call DEC();
}

atomic action {:layer 2} MAIN' ()
{
}

////////////////////////////////////////////////////////////////////////////////

async left action {:layer 1} INC ()
modifies x;
{
  x := x + 1;
}

async left action {:layer 1} DEC ()
modifies x;
{
  x := x - 1;
}
