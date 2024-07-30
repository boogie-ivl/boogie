// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x : int;

left action {:layer 1} inc ()
modifies x;
{ x := x + 1; }

// Error: Gate failure of ass_eq_1 not preserved by inc
atomic action {:layer 1} ass_eq_1 ()
{ assert x == 1; }

// Correct
atomic action {:layer 1} ass_leq_1 ()
{ assert x <= 1; }

// Error: init and inc do not commute
atomic action {:layer 1} init ()
modifies x;
{ x := 0; }

////////////////////////////////////////////////////////////////////////////////

// Error block is blocking
left action {:layer 2} block ()
{ assume x >= 0; }

pure action F (i: int) returns ({:pool "A"} j: int)
asserts {:add_to_pool "A", i+1} true;
{
  assume j > i;
}