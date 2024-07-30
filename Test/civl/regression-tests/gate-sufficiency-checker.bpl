// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} x: int;

atomic action {:layer 1} Foo()
asserts x > 0;
{
    assert x != 0;
}