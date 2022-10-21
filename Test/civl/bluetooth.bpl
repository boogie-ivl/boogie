// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
This example is inspired by coordination seen in device drivers.
A stopping thread is attempting to clean up driver resources and
forces user threads to exit the driver and not re-enter. This proof
works for arbitrary number of user threads.

This example provides another instance of permission redistribution;
see cav2020-3.bpl for another example inspired by a concurrent
garbage collector.
*/

type {:datatype} Perm;
function {:constructor} Left(i: int): Perm;
function {:constructor} Right(i: int): Perm;

function Size<T>(set: [T]bool): int;
axiom {:ctor "Lset"} (forall<T> set: [T]bool :: Size(set) >= 0);

procedure {:lemma} SizeLemma<T>(X: [T]bool, x: T);
ensures Size(X[x := false]) + 1 == Size(X[x := true]);

procedure {:lemma} SubsetSizeRelationLemma<T>(X: [T]bool, Y: [T]bool);
requires MapImp(X, Y) == MapConst(true);
ensures X == Y || Size(X) < Size(Y);

var {:layer 0,3} stoppingFlag: bool;
var {:layer 0,2} stopped: bool;
var {:layer 1,2} usersInDriver: Lset Perm;
var {:layer 0,1} pendingIo: int;
var {:layer 0,1} stoppingEvent: bool;

procedure {:yield_invariant} {:layer 2} Inv2();
requires stopped ==> stoppingFlag;

procedure {:yield_invariant} {:layer 1} Inv1();
requires stoppingEvent ==> stoppingFlag && usersInDriver->dom == MapConst(false);
requires pendingIo == Size(usersInDriver->dom) + (if stoppingFlag then 0 else 1);

// user code

procedure {:yields} {:layer 2}
{:yield_preserves "Inv2"}
{:yield_preserves "Inv1"}
User(i: int, {:layer 1,2} {:linear_in} ps: Lset Perm)
requires {:layer 2} ps->dom[Left(i)] && ps->dom[Right(i)];
{
    var {:layer 1,2} ps': Lset Perm;

    ps' := ps;
    while (*)
    invariant {:yields} {:layer 2} {:yield_loop "Inv2"} ps'->dom[Left(i)] && ps'->dom[Right(i)];
    invariant {:yields} {:layer 1} {:yield_loop "Inv1"} true;
    {
        call ps' := Enter#1(i, ps');
        call CheckAssert#1(i, ps');
        call ps' := Exit(i, ps');
    }
}

procedure {:atomic} {:layer 2} AtomicEnter#1(i: int, {:linear_in} ps: Lset Perm) returns (ps': Lset Perm)
modifies usersInDriver;
{
    assume !stoppingFlag;
    call ps' := AddToBarrier(i, ps);
}
procedure {:yields} {:layer 1} {:refines "AtomicEnter#1"}
{:yield_preserves "Inv1"}
Enter#1(i: int, {:layer 1} {:linear_in} ps: Lset Perm) returns ({:layer 1} ps': Lset Perm)
{
    call Enter();
    call {:layer 1} SizeLemma(usersInDriver->dom, Left(i));
    call ps' := AddToBarrier(i, ps);
}

procedure {:left} {:layer 2} AtomicCheckAssert#1(i: int, ps: Lset Perm)
{
    assert ps->dom[Right(i)] && usersInDriver->dom[Left(i)];
    assert !stopped;
}
procedure {:yields} {:layer 1} {:refines "AtomicCheckAssert#1"}
{:yield_preserves "Inv1"}
CheckAssert#1(i: int, {:layer 1} ps: Lset Perm)
{
    call CheckAssert();
}

procedure {:left} {:layer 2} AtomicExit(i: int, {:linear_in} ps: Lset Perm) returns (ps': Lset Perm)
modifies usersInDriver;
{
    assert ps->dom[Right(i)] && usersInDriver->dom[Left(i)];
    call ps' := RemoveFromBarrier(i, ps);
}
procedure {:yields} {:layer 1} {:refines "AtomicExit"}
{:yield_preserves "Inv1"}
Exit(i: int, {:layer 1} {:linear_in} ps: Lset Perm) returns ({:layer 1} ps': Lset Perm)
{
    call DeleteReference();
    call {:layer 1} SizeLemma(usersInDriver->dom, Left(i));
    call ps' := RemoveFromBarrier(i, ps);
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver->dom);
}

// stopper code

procedure {:yields} {:layer 2} {:refines "AtomicSetStoppingFlag"}
{:yield_preserves "Inv2"}
{:yield_preserves "Inv1"}
Stopper(i: Lval int)
{
    call Close(i);
    call WaitAndStop();
}

procedure {:yields} {:layer 1} {:refines "AtomicSetStoppingFlag"}
{:yield_preserves "Inv1"}
Close(i: Lval int)
{
    call SetStoppingFlag(i);
    call DeleteReference();
    call {:layer 1} SubsetSizeRelationLemma(MapConst(false), usersInDriver->dom);
}

procedure {:atomic} {:layer 2} AtomicWaitAndStop()
modifies stopped;
{
    assume usersInDriver->dom == MapConst(false);
    stopped := true;
}
procedure {:yields} {:layer 1} {:refines "AtomicWaitAndStop"}
{:yield_preserves "Inv1"}
WaitAndStop()
{
    call WaitOnStoppingEvent();
    call SetStopped();
}

/// introduction actions

procedure {:intro} {:layer 1, 2} AddToBarrier(i: int, {:linear_in} ps: Lset Perm) returns (ps': Lset Perm)
modifies usersInDriver;
{
    var x: Lval Perm;
    ps' := ps;
    call x := Lval_Split(Left(i), ps');
    call Lval_Transfer(x, usersInDriver);
}

procedure {:intro} {:layer 1, 2} RemoveFromBarrier(i: int, {:linear_in} ps: Lset Perm) returns (ps': Lset Perm)
modifies usersInDriver;
{
    var x: Lval Perm;
    ps' := ps;
    call x := Lval_Split(Left(i), usersInDriver);
    call Lval_Transfer(x, ps');
}

/// primitive actions

procedure {:atomic} {:layer 1} AtomicEnter()
modifies pendingIo;
{
    assume !stoppingFlag;
    pendingIo := pendingIo + 1;
}
procedure {:yields} {:layer 0} {:refines "AtomicEnter"} Enter();

procedure {:atomic} {:layer 1} AtomicCheckAssert()
{
    assert !stopped;
}
procedure {:yields} {:layer 0} {:refines "AtomicCheckAssert"} CheckAssert();

procedure {:right} {:layer 1,3} AtomicSetStoppingFlag(i: Lval int)
modifies stoppingFlag;
{
    // The first assertion ensures that there is at most one stopper.
    // Otherwise AtomicSetStoppingFlag does not commute with itself.
    assert i->val == 0;
    assert !stoppingFlag;
    stoppingFlag := true;
}
procedure {:yields} {:layer 0} {:refines "AtomicSetStoppingFlag"} SetStoppingFlag(i: Lval int);

procedure {:atomic} {:layer 1} AtomicDeleteReference()
modifies pendingIo, stoppingEvent;
{
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
        stoppingEvent := true;
    }
}
procedure {:yields} {:layer 0} {:refines "AtomicDeleteReference"} DeleteReference();

procedure {:atomic} {:layer 1} AtomicWaitOnStoppingEvent()
{
    assume stoppingEvent;
}
procedure {:yields} {:layer 0} {:refines "AtomicWaitOnStoppingEvent"} WaitOnStoppingEvent();

procedure {:left} {:layer 1} AtomicSetStopped()
modifies stopped;
{
    stopped := true;
}
procedure {:yields} {:layer 0} {:refines "AtomicSetStopped"} SetStopped();
