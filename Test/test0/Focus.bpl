// RUN: %boogie /vcsDumpSplits "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff Ex.split.-1.bpl Ex.split.-1.bpl
// RUN: %diff Ex.split.0.bpl Ex.split.0.bpl
// RUN: %diff Ex.split.1.bpl Ex.split.1.bpl
// RUN: %diff Ex.split.2.bpl Ex.split.2.bpl
// RUN: %diff Ex.split.3.bpl Ex.split.3.bpl
// RUN: %diff Ex.split.4.bpl Ex.split.4.bpl

procedure Ex() returns (y: int)
  ensures y >= 0;
{
  var x: int;
  x := 5;
  y := 0;
  while (x > 0)
    invariant x + y == 5;
    invariant x*x <= 25;
  {
    x := x - 1;
    assert {:focus} (x+y) * (x+y) > 25;
    y := y + 1;
    if (x < 3) {
      assert 2 < 2;
      assert {:focus} y*y > 4;
    }
    else {
      assert {:focus} y*y*y < 8;
      assert 2 < 2;
    }
    assert {:focus} (x+y) * (x+y) == 25;
  }
}
