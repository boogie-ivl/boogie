// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,3} x:int;

yield procedure {:layer 2} Client ()
refines A_Inc;
{
  call Service();
}

atomic action {:layer 1} A_Service()
refines A_Inc;
creates A_Inc;
{
  async call A_Inc();
}
yield procedure {:layer 0} Service ()
refines A_Service;
{
  async call Callback();
}

async both action {:layer 1,3} A_Inc ()
modifies x;
{ x := x + 1; }
yield procedure {:layer 0} Callback ();
refines A_Inc;
