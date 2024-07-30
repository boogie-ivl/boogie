// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} Good()
{
    async call {:skip} P_A();
}

atomic action {:layer 1} A()
asserts true;
{}

yield procedure {:layer 0} P_A();
refines A;

yield procedure {:layer 1} Bad()
{
    async call {:skip} P_B();
}

atomic action {:layer 1} B()
asserts false;
{}

yield procedure {:layer 0} P_B();
refines B;