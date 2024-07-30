// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear} g: One int;

async left action {:layer 1} main_f''({:linear_in} l: One int)
refines final using Inv;
creates main_f'';
{
  if (*) {
  } else {
    async call main_f''(l);
  }
}

action {:layer 2} final({:linear_in} l: One int)
{
  // conclusion check succeeds due to disjointness assumption
}

action {:layer 1} Inv({:linear_in} l: One int)
creates main_f'';
{
  assert l != g;
  if (*) {
  } else {
    async call main_f''(l);
    call set_choice(main_f''(l));
  }
}