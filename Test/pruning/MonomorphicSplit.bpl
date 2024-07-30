// RUN: %parallel-boogie /prune:1 /errorTrace:0 /printSplit:"%t" /printSplitDeclarations "%s" > "%t"
// RUN: %OutputCheck "%s" --file-to-check="%t-monomorphicSplit--1.spl"

// The following checks are a bit simplistic, but this is
// on purpose to reduce brittleness. We assume there would now be two uses clauses
// with one axiom each, and those axioms should not be a conjunction of
// the instantiations of the original axiom.
// 
// Last CHECK-NOT is for ensuring definition axioms are not printed outside
// uses clauses when using /printSplitDeclarations.

// CHECK-L: uses
// CHECK-NEXT-L: axiom
// CHECK-NOT-L: &&
// CHECK-L: }
// CHECK-L: uses
// CHECK-NEXT-L: axiom
// CHECK-NOT-L: &&
// CHECK-L: }
// CHECK-NOT: axiom

// Related PR #767.

function f1 <T> (x: T) : int uses {
  axiom (forall <T> x: T :: {f1(x)} f1(x) == 42);
}

// Both f1 and the axiom will be monomorphized into bool and int instances.
// Automatic edge inference would already ensure that only the monomorphized instances
// are incoming, however we want to test here how the new uses clauses are determined.
//
// After instantiation, each instance of f1 for some T should *only* have 
// the T-instantiated axiom as outgoing. 

procedure monomorphicSplit()
  ensures f1(true) == 42;
  ensures f1(3) == 42;
{
}
