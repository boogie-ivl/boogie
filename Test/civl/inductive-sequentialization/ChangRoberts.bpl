// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N: int; // size of the ring
axiom N > 0;
function {:inline} Next(i: int) : int { (i + 1) mod N }
function {:inline} Prev(i: int) : int { (i - 1) mod N }

function {:inline} ValidPid(pid: int) : bool { 0 <= pid && pid < N }

var {:layer 0,4} leader: [int]bool;       // leader[pid] iff pid is a leader

// priority for becoming leader (ties are broken by pid)
function Priority(int): int;      // pid -> priority
function {:inline} Below(self: int, pid: int): bool
{
  Priority(self) < Priority(pid) || 
  (Priority(self) == Priority(pid) && self < pid)
}

const ExpectedLeader: int;
axiom ValidPid(ExpectedLeader);
axiom (forall i: int:: ValidPid(i) ==> i == ExpectedLeader || Below(i, ExpectedLeader));

// alternative coordinates for identifying processes where ExpectedLeader is at position 0
// Pos converts from process id to its position
// Pid converts from position to process id
function {:inline} Pos(pid: int) : int { (pid - ExpectedLeader) mod N }
function {:inline} Pid(pos: int) : int { (ExpectedLeader + pos) mod N }

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init(pids: [int]bool, leader: [int]bool) : bool
{
  pids == MapConst(true) &&
  leader == MapConst(false)
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 4} MAIN3(pids: Set int)
modifies leader;
{
  assert Init(pids->val, leader);
  leader := MapConst(false)[ExpectedLeader := true];
}

action {:layer 3} INV2 (pids: Set int)
creates P;
modifies leader;
{
  /*
  Invariant description:
  
  A (possibly empty) prefix of pending asyncs starting at position 0 is created.
  The i-th pending async is created by process at position i and is targeted at 
  the process at position Next(i).

  A singleton pending async P(self, pid) is also created such that the position of
  process pid is the length of the aforementioned prefix and self is a target whose
  position is ahead of pid. This is the pending async chosen to be scheduled.
  */
  var {:pool "INV2"} choice: P; // nondeterministically chosen leading pending async
  var self, pid: int;

  assert Init(pids->val, leader);
  assume {:add_to_pool "INV2", P(Next(choice->self), choice->pid), P(choice->pid, Prev(choice->pid))} true;
  if (*) {
    P(self, pid) := choice;
    assume ValidPid(self) && ValidPid(pid);
    // self is ahead of pid and may have wrapped around to position 0
    assume Pos(self) == 0 || Pos(pid) < Pos(self);
    // summarize the result of all priority comparisons by the leading pending async
    // wraparound to position 0 is handled carefully
    assume (forall {:pool "ORDER"} x: int :: {:add_to_pool "ORDER", x} Pos(pid) < x && x <= Prev(Pos(self)) ==> Below(Pid(x), pid));
    // create prefix
    call create_asyncs(
      (lambda pa: P :: ValidPid(pa->pid) && Pos(pa->pid) < Pos(pid) && pa->self == Next(pa->pid)));
    // create singleton and set the choice
    async call P(self, pid);
    call set_choice(choice);
  } else {
    leader[ExpectedLeader] := true;
  }
}
////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 3} MAIN2(pids: Set int)
refines MAIN3 using INV2;
creates P;
{
  assert Init(pids->val, leader);
  assume {:add_to_pool "INV2", P(ExpectedLeader, Prev(ExpectedLeader))} true;
  call create_asyncs(
    (lambda pa: P :: ValidPid(pa->pid) && pa->self == Next(pa->pid)));
}

action {:layer 2} INV1({:linear_in} pids: Set int)
creates PInit, P;
{
  var {:pool "INV1"} k: int;
  assert Init(pids->val, leader);

  assume
    {:add_to_pool "INV1", k+1}
    {:add_to_pool "PInit", PInit(k)}
    0 <= k && k <= N;
  call create_asyncs((lambda {:pool "PInit"} pa: PInit :: k <= pa->self && pa->self < N));
  call create_asyncs((lambda pa: P :: 0 <= pa->pid && pa->pid < k && pa->self == Next(pa->pid)));
  call set_choice(PInit(k));
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 2} MAIN1(pids: Set int)
refines MAIN2 using INV1;
creates PInit;
{
  assert Init(pids->val, leader);
  assume {:add_to_pool "INV1", 0} true;
  call create_asyncs((lambda pa: PInit :: ValidPid(pa->self)));
}

async left action {:layer 2} PInit(self: int)
creates P;
{
  assert ValidPid(self);
  async call P(Next(self), self);
}

async atomic action {:layer 2, 3} P(self: int, pid: int)
creates P;
modifies leader;
{
  assert ValidPid(self) && ValidPid(pid);
  if (self == pid)
  {
    leader[pid] := true;
  }
  else if (Below(self, pid))
  {
    async call P(Next(self), pid);
  }
}

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 1} main(pids: Set int)
refines MAIN1;
{
  var {:pending_async}{:layer 1} PAs: [PInit]int;
  var pids': Set int;
  var i: int;

  pids' := pids;
  i := 0;
  while (i < N)
  invariant {:layer 1} 0 <= i && i <= N;
  invariant {:layer 1} (forall ii:int :: ValidPid(ii) && ii >= i ==> Set_Contains(pids', ii));
  invariant {:layer 1} PAs == (lambda pa: PInit :: if ValidPid(pa->self) && pa->self < i then 1 else 0);
  {
    pids' := Set_Remove(pids', i);
    async call pinit(i);
    i := i + 1;
  }
}

yield procedure {:layer 1} pinit(self: int)
refines PInit;
requires {:layer 1} ValidPid(self);
{
  async call p(Next(self), self);
}

yield procedure {:layer 1} p(self: int, pid: int)
refines P;
requires {:layer 1} ValidPid(self) && ValidPid(pid);
{
  if (self == pid)
  {
    call set_leader(pid);
  }
  else if (Below(self, pid))
  {
    async call p(Next(self), pid);
  }
}

////////////////////////////////////////////////////////////////////////////////

both action {:layer 1} SET_LEADER(pid: int)
modifies leader;
{
  leader[pid] := true;
}
yield procedure {:layer 0} set_leader(pid: int);
refines SET_LEADER;
