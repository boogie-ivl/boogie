// RUN: %boogie /printSplit:- /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure IsolateReturn(x: int, y: int) returns (r: int)
  ensures r > 4;
{
  r := 0;
  if (x > 0) {
    r := r + 1;
  } else {
    r := r + 2;
  }
  
  if (y > 0) {
    r := r + 3;
    return {:isolate};
  }
  
  r := r + 4;
}

procedure IsolateReturnPaths(x: int, y: int) returns (r: int)
  ensures r > 4;
{
  r := 0;
  if (x > 0) {
    r := r + 1;
  } else {
    r := r + 2;
  }
  
  if (y > 0) {
    r := r + 3;
    return {:isolate "paths"};
  }
  
  r := r + 4;
}