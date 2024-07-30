// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

////////////////////////////////////////////////////////////////////////////////

async atomic action {:layer 1,2} A () {}

left action {:layer 1} B ()
creates A;
{
  async call A();
}

left action {:layer 1} C (flag:bool)
creates A;
{
  if (flag) {
    async call A();
  }
}

yield procedure {:layer 0} b ();
refines B;

yield procedure {:layer 0} c (flag:bool);
refines C;


////////////////////////////////////////////////////////////////////////////////

// Verifies
yield procedure {:layer 1} test1 ()
refines TEST1;
{
  call b();
  call b();
}

atomic action {:layer 2} TEST1 ()
creates A;
{
  call create_multi_asyncs(MapConst(0)[A() := 2]);
}

////////////////////////////////////////////////////////////////////////////////

// Fails
yield procedure {:layer 1} test2 ()
refines TEST2;
{
  call b();
  call b();
}

atomic action {:layer 2} TEST2 ()
creates A;
{
  async call A();
}

////////////////////////////////////////////////////////////////////////////////

// Fails
yield procedure {:layer 1} test3 ()
refines TEST3;
{
  call c(true);
}

atomic action {:layer 2} TEST3 () returns () {}

////////////////////////////////////////////////////////////////////////////////

// Verifies
yield procedure {:layer 1} test4 ()
refines TEST4;
{
  call c(false);
}

atomic action {:layer 2} TEST4 () returns () {}

////////////////////////////////////////////////////////////////////////////////

// Verifies
yield procedure {:layer 1} test5 ()
refines TEST5;
{
  var i:int;
  var {:pending_async}{:layer 1} PAs:[A]int;

  i := 0;
  while (i < 10)
  invariant {:layer 1} 0 <= i && i <= 10;
  invariant {:layer 1} PAs == MapConst(0)[A() := i];
  {
    call b();
    i := i + 1;
  }
}

atomic action {:layer 2} TEST5 ()
creates A;
{
  call create_multi_asyncs(MapConst(0)[A() := 10]);
}
