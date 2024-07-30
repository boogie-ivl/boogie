// RUN: %parallel-boogie /printSplit:%t "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff %S/Foo.split.0.bpl.expect %t-Foo-0.spl
// RUN: %diff %S/Foo.split.1.bpl.expect %t-Foo-1.spl
// RUN: %diff %S/Foo.split.2.bpl.expect %t-Foo-2.spl

procedure Foo()
{
  if (*) { 
    assert 2 == 1 + 1; 
    assume false; 
  } 
  assume 2 == 1 + 1; 
  assert {:split_here} 2 == 2;
  assert {:split_here} 3 == 2 + 1;
  assert 1 == 1;
}
