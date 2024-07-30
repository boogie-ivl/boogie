// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Tid = int;

const nil:Tid;
var {:layer 0,4} l:Tid;
var {:layer 0,5} x:int;

atomic action {:layer 5} A_Client ()
modifies x;
{
  x := x + 1;
}
yield procedure {:layer 4} Client({:hide}{:linear_in} tid: One Tid)
refines A_Client;
requires {:layer 4} tid->val != nil;
{
  call GetLockAndCallback(tid);
}

atomic action {:layer 4} A_GetLockAndCallback' ({:linear_in} tid: One Tid)
modifies x;
{
  assert tid->val != nil;
  x := x + 1;
}

async left action {:layer 3} A_Callback ({:linear_in} tid: One Tid)
modifies l, x;
{
  assert tid->val != nil && l == tid->val;
  x := x + 1;
  l := nil;
}
yield procedure {:layer 2} Callback ({:linear_in} tid: One Tid)
refines A_Callback;
{
  var tmp:int;
  call tmp := read_x_lock(tid);
  call write_x_lock(tmp+1, tid);
  async call {:sync} ReleaseLock(tid);
}

both action {:layer 2} A_read_x_lock ({:linear} tid: One Tid) returns (v:int)
{ assert tid->val != nil && l == tid->val; v := x; }
yield procedure {:layer 1} read_x_lock ({:linear} tid: One Tid) returns (v:int)
refines A_read_x_lock;
{ call v := read_x(); }

both action {:layer 2} A_write_x_lock (v:int, {:linear} tid: One Tid)
modifies x;
{ assert tid->val != nil && l == tid->val; x := v; }
yield procedure {:layer 1} write_x_lock (v:int, {:linear} tid: One Tid)
refines A_write_x_lock;
{ call write_x(v); }

atomic action {:layer 1} A_read_x () returns (v:int)
{ v := x; }
yield procedure {:layer 0} read_x () returns (v:int);
refines A_read_x;

atomic action {:layer 1} A_write_x (v:int)
modifies x;
{ x := v; }
yield procedure {:layer 0} write_x (v:int);
refines A_write_x;

// -----------------------------------------------------------------------------

atomic action {:layer 3}
A_GetLockAndCallback ({:linear_in} tid: One Tid)
refines A_GetLockAndCallback';
creates A_Callback;
modifies l;
{
  assert tid->val != nil;
  assume l == nil;
  l := tid->val;
  async call A_Callback(tid);
}
yield procedure {:layer 2} GetLockAndCallback ({:linear_in} tid: One Tid)
refines A_GetLockAndCallback;
{
  call GetLock(tid);
  async call Callback(tid);
}

atomic action {:layer 2} A_GetLock ({:linear} tid: One Tid)
modifies l;
{
  assert tid->val != nil;
  assume l == nil;
  l := tid->val;
}
yield procedure {:layer 1} GetLock ({:linear} tid: One Tid)
refines A_GetLock;
{
  var success:bool;
  while (true)
  invariant {:yields} true;
  {
    call success := cas_l(nil, tid->val);
    if (success) {
      return;
    }
  }
}

left action {:layer 2} A_ReleaseLock ({:linear_in} tid: One Tid)
modifies l;
{
  assert tid->val != nil && l == tid->val;
  l := nil;
}
yield procedure {:layer 1} ReleaseLock ({:linear_in} tid: One Tid)
refines A_ReleaseLock;
{
  call write_l(nil);
}

atomic action {:layer 1} A_cas_l (oldval:Tid, newval:Tid) returns (success:bool)
modifies l;
{
  if (l == oldval) {
    l := newval;
    success := true;
  } else {
    success := false;
  }
}
yield procedure {:layer 0} cas_l (oldval:Tid, newval:Tid) returns (success:bool);
refines A_cas_l;

atomic action {:layer 1} A_write_l (v:Tid)
modifies l;
{ l := v; }
yield procedure {:layer 0} write_l (v:Tid);
refines A_write_l;
