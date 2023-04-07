// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ref;
type Field A B;
type HeapType = <A, B> [Ref, Field A B]B; // Using type parameters and the ==> operator can trigger the OpTypeEraser visitor which can cause stack overflows.

procedure foo(n: int)
  requires true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
  || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
  true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
    || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
    true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
      || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
      true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
        || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
        true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
          || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
          true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true
            || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true || true ||
            n == 2;
  requires true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
  ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
  true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
    ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
    true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
      ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
      true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
        ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
        true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
          ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
          true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
            ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
            ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
              ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
              true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                  ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                  true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                    ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                    true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                      ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                      true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                        ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                        ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                          ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                          true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                            ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                            true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                              ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                              true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                                ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                                true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                                  ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==>
                                  true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true
                                    ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true ==> true;
                                    
{
  if (n == 2) {
    if (n == 2) {
      if (n == 2) {
        if (n == 2) {
          if (n == 2) {
            if (n == 2) {
              if (n == 2) {
                if (n == 2) {
                  if (n == 2) {
                    if (n == 2) {
                      if (n == 2) {
                        if (n == 2) {
                          if (n == 2) {
                            if (n == 2) {
                              if (n == 2) {
                                if (n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2
                                    && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2 && n == 2  ) {
                                  assert n == 3;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
