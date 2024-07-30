// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: batch_mode

// This is identical to "rec-IS1.bpl", 
// but with the {:IS_right} attribute

async left action {:layer 1} main_f''()
refines {:IS_right} final using Inv;
creates main_f'';
{
    if (*) {
    }
    else {
      async call main_f''();
    }
}

left action {:layer 2} final()
{
  
}

action {:layer 1} Inv()
creates main_f'';
{
    if (*) {
    }
    else {
      async call main_f''();
      call set_choice(main_f''());
    }
}