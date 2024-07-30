// RUN: %parallel-boogie /printSplit:%t /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
    assert {:split_here} (x+y) * (x+y) > 16; // should not lead to more than one split.
    assert {:focus} (x+y) * (x+y) > 25;
    y := y + 1;
    if (x < 3) {
      assert 2 < 2;
      assert {:focus} y*y > 4;
    }
    else {
      assert 2 < 2;
    }
    assert {:focus} (x+y) * (x+y) == 25;
  }
}

procedure focusInconsistency(x : int) returns (y: int)
  ensures false;
{
  var i: int where false;

  if (x > 0) {
    havoc i; // mentioning i in this branch results in assuming false because of the where clause.
             // Thus, the post-condition proves for this path.
  } else {
    assume {:focus} true; // i is not mentioned in this branch so the where clause is not assumed for it.
  }
}
