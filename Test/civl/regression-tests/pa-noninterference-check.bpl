// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

atomic action {:layer 3} A_Foo()
creates A_Incr;
{
    async call A_Incr();
}

yield procedure {:layer 2} Foo()
refines A_Foo;
{
    async call Incr();
}

async atomic action {:layer 1,3} A_Incr()
modifies x;
{
    x := x + 1;
}

yield procedure {:layer 0} Incr();
refines A_Incr;

yield invariant {:layer 1} Inv();
invariant x == 0;

var {:layer 0,3} x: int;

yield procedure {:layer 1} Bar()
preserves call Inv();
{ }
