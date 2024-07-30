// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} foo()
requires false;
ensures false;
{
  assert false;
}

action {:layer 1} bar()
requires false;
{ }

atomic action {:layer 1} A()
requires {:layer 2} false;
{}

