// Can't use %parallel-boogie here yet - see https://github.com/boogie-org/boogie/issues/460
// RUN: %boogie -xml:"%t.xml" "%s"
// Chop off the first line, since OutputCheck expects ASCII and can't handle the byte-order mark
// RUN: tail -n +2 "%t.xml" > "%t.trimmed.xml"
// RUN: %OutputCheck "%s" --file-to-check="%t.trimmed.xml"
// CHECK: \<method name="ExampleWithSplits" startTime=".*"\>
// CHECK:   \<split number="1" startTime=".*"\>
// CHECK:     \<conclusion duration=".*" outcome="valid" />
// CHECK:   \</split\>
// CHECK:   \<split number="2" startTime=".*"\>
// CHECK:     \<conclusion duration=".*" outcome="valid" />
// CHECK:   \</split\>
// CHECK:   \<conclusion endTime=".*" duration=".*" outcome="correct" />
// CHECK: \</method\>
// CHECK: \<method name="ExampleWithoutSplits" startTime=".*"\>
// CHECK:   \<conclusion endTime=".*" duration=".*" outcome="correct" />
// CHECK: \</method\>
// CHECK: \<method name="AnotherExampleWithoutSplits" startTime=".*"\>
// CHECK:   \<conclusion endTime=".*" duration=".*" outcome="correct" />
// CHECK: \</method\>

procedure ExampleWithSplits()
{
  assert 1 + 1 == 2;
  assume {:split_here} true;
  assert 2 + 2 == 4;
}

procedure ExampleWithoutSplits()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}

procedure AnotherExampleWithoutSplits()
{
  assert 1 + 1 == 2;
  assert 2 + 2 == 4;
}
