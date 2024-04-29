// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} g: int;

yield procedure {:layer 1} foo()
requires {:layer 1} g > 0;
ensures {:layer 1} g > 0;
{ }

atomic action {:layer 1} A()
requires {:layer 1} g > 0;
{}