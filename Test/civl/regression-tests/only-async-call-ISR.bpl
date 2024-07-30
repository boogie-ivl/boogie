// RUN: %parallel-boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
yield procedure {:layer 2} proc()
{
    call _main_f();
}

async action {:layer 2,3} main_f'()
{
  
}

async action {:layer 1} main_f()
refines {:IS_right} main_f' using Inv;
creates main_f;
{
    if (*) {
    }
    else {
      async call main_f();
    }
}

yield procedure {:layer 0} _main_f();
refines main_f;

action {:layer 1} Inv()
creates main_f;
{
    if (*) {
    }
    else {
      async call main_f();
      call set_choice(main_f());
    }
}