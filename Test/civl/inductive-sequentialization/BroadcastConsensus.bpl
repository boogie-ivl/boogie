// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const n:int;
axiom n >= 1;

type val = int;
type pid = int;

datatype perm {
  Broadcast(i: int),
  Collect(i: int)
}

function {:inline} pid(i:int) : bool { 1 <= i && i <= n }

function {:inline} InitialBroadcastPAs (k:pid) : [BROADCAST]bool
{
  (lambda pa:BROADCAST :: pa->p->val == Broadcast(pa->i) && pid(pa->i) && pa->i < k)
}

function {:inline} InitialCollectPAs (k:pid) : [COLLECT]bool
{
  (lambda pa:COLLECT :: pa->p->val == Collect(pa->i) && pid(pa->i) && pa->i < k)
}

function {:inline} AllBroadcasts () : [BROADCAST]bool
{ (lambda pa:BROADCAST :: pa->p->val == Broadcast(pa->i) && pid(pa->i)) }

function {:inline} AllCollects () : [COLLECT]bool
{ (lambda pa:COLLECT :: pa->p->val == Collect(pa->i) && pid(pa->i)) }

function {:inline} RemainingBroadcasts (k:pid) : [BROADCAST]bool
{ (lambda {:pool "Broadcast"} pa:BROADCAST :: pa->p->val == Broadcast(pa->i) && k < pa->i && pa->i <= n) }

function {:inline} RemainingCollects (k:pid) : [COLLECT]bool
{ (lambda {:pool "Collect"} pa:COLLECT :: pa->p->val == Collect(pa->i) && k < pa->i && pa->i <= n) }

////////////////////////////////////////////////////////////////////////////////

var {:layer 0,1} CH_low:[pid][val]int;
var {:layer 1,4} CH:[val]int;
var {:layer 0,4} value:[pid]val;
var {:layer 0,4} decision:[pid]val;

function max(CH:[val]int) : val;
function card(CH:[val]int) : int;

axiom card(MultisetEmpty) == 0;
axiom (forall CH:[val]int, v:val, x:int :: card(CH[v := x]) == card(CH) + x - CH[v]);
axiom (forall m:[val]int, m':[val]int :: MultisetSubsetEq(m, m') && card(m) == card(m') ==> m == m');

axiom (forall v:val :: max(MultisetSingleton(v)) == v);
axiom (forall CH:[val]int, v:val, x:int :: x > 0 ==> max(CH[v := x]) == (if v > max(CH) then v else max(CH)));

function value_card(v:val, value:[pid]val, i:pid, j:pid) : int
{
  if j < i then
    0
  else
    if value[j] == v then
      value_card(v, value, i, j-1) + 1
    else
      value_card(v, value, i, j-1)
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 4}
MAIN''({:linear_in} ps: Set perm)
modifies CH, decision;
{
  assert ps->val == (lambda p:perm :: pid(p->i));
  assert CH == MultisetEmpty;
  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  decision := (lambda i:pid :: if pid(i) then max(CH) else old(decision)[i]);
}

action {:layer 3}
INV_COLLECT_ELIM({:linear_in} ps: Set perm)
creates COLLECT;
modifies CH, decision;
asserts ps->val == (lambda p:perm :: pid(p->i));
asserts CH == MultisetEmpty;
{
  var {:linear} ps': Set perm;
  var {:linear} remainingCollects: Set perm;
  var {:pool "INV_COLLECT"} k: int;

  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  assume
    {:add_to_pool "INV_COLLECT", k, k+1}
    {:add_to_pool "Collect", COLLECT(One(Collect(n)), n)}
    0 <= k && k <= n;
  decision := (lambda i:pid :: if 1 <= i && i <= k then max(CH) else decision[i]);
  ps' := ps;
  call remainingCollects := Set_Get(ps', (lambda p: perm :: p is Collect && k < p->i && p->i <= n));
  call {:linear remainingCollects} create_asyncs(RemainingCollects(k));
  call set_choice(COLLECT(One(Collect(k+1)), k+1));
}

////////////////////////////////////////////////////////////////////////////////

atomic action {:layer 3}
MAIN'({:linear_in} ps: Set perm)
refines MAIN'' using INV_COLLECT_ELIM;
creates COLLECT;
modifies CH;
asserts ps->val == (lambda p:perm :: pid(p->i));
asserts CH == MultisetEmpty;
{
  var {:linear} ps': Set perm;
  var {:linear} allCollects: Set perm;

  assume {:add_to_pool "INV_COLLECT", 0} true;
  CH := (lambda v:val :: value_card(v, value, 1, n));
  assume card(CH) == n;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  ps' := ps;
  call allCollects := Set_Get(ps', (lambda p: perm :: p is Collect && pid(p->i)));
  call {:linear allCollects} create_asyncs(AllCollects());
}

atomic action {:layer 2}
MAIN({:linear_in} ps: Set perm)
refines MAIN' using INV_BROADCAST_ELIM;
creates BROADCAST, COLLECT;
asserts ps->val == (lambda p:perm :: pid(p->i));
asserts CH == MultisetEmpty;
{
  var {:linear} ps': Set perm;
  var {:linear} allBroadcasts: Set perm;
  var {:linear} allCollects: Set perm;

  assume {:add_to_pool "INV_BROADCAST", 0} true;
  ps' := ps;
  call allBroadcasts := Set_Get(ps', (lambda p: perm :: p is Broadcast && pid(p->i)));
  call {:linear allBroadcasts} create_asyncs(AllBroadcasts());
  call allCollects := Set_Get(ps', (lambda p: perm :: p is Collect && pid(p->i)));
  call {:linear allCollects} create_asyncs(AllCollects());
}

action {:layer 2}
INV_BROADCAST_ELIM({:linear_in} ps: Set perm)
creates BROADCAST, COLLECT;
modifies CH;
asserts ps->val == (lambda p:perm :: pid(p->i));
asserts CH == MultisetEmpty;
{
  var {:linear} ps': Set perm;
  var {:linear} remainingBroadcasts: Set perm;
  var {:linear} allCollects: Set perm;
  var {:pool "INV_BROADCAST"} k: int;

  assume
    {:add_to_pool "INV_BROADCAST", k, k+1}
    {:add_to_pool "Broadcast", BROADCAST(One(Broadcast(n)), n)}
    0 <= k && k <= n;
  CH := (lambda v:val :: value_card(v, value, 1, k));
  assume card(CH) == k;
  assume MultisetSubsetEq(MultisetEmpty, CH);
  ps' := ps;
  call remainingBroadcasts := Set_Get(ps', (lambda p: perm :: p is Broadcast && k < p->i && p->i <= n));
  call {:linear remainingBroadcasts} create_asyncs(RemainingBroadcasts(k));
  call allCollects := Set_Get(ps', (lambda p: perm :: p is Collect && pid(p->i)));
  call {:linear allCollects} create_asyncs(AllCollects());
  call set_choice(BROADCAST(One(Broadcast(k+1)), k+1));
}

async left action {:layer 2} BROADCAST({:linear_in} p: One perm, i:pid)
modifies CH;
{
  assert pid(i) && p->val == Broadcast(i);
  CH := CH[value[i] := CH[value[i]] + 1];
}

async atomic action {:layer 2,3} COLLECT({:linear_in} p: One perm, i:pid)
modifies decision;
requires call YieldCollect();
{
  var received_values:[val]int;
  assert pid(i) && p->val == Collect(i);
  assume card(received_values) == n;
  assume MultisetSubsetEq(MultisetEmpty, received_values);
  assume MultisetSubsetEq(received_values, CH);
  decision[i] := max(received_values);
}

yield invariant {:layer 3} YieldCollect();
invariant CH == (lambda v:val :: value_card(v, value, 1, n));
invariant card(CH) == n;
invariant MultisetSubsetEq(MultisetEmpty, CH);

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1} YieldInv();
invariant Inv(CH_low, CH);

function {:inline} Inv(CH_low:[pid][val]int, CH:[val]int) : bool
{
  (forall i:pid :: MultisetSubsetEq(MultisetEmpty, CH_low[i]) && MultisetSubsetEq(CH_low[i], CH))
}

pure procedure {:inline 1} add_to_multiset (CH:[val]int, x: val) returns (CH':[val]int)
{
  CH' := CH[x := CH[x] + 1];
}

////////////////////////////////////////////////////////////////////////////////

yield invariant {:layer 1}
YieldInit({:linear} ps: Set perm);
invariant ps->val == (lambda p:perm :: pid(p->i));
invariant (forall ii:pid :: CH_low[ii] == MultisetEmpty);
invariant CH == MultisetEmpty;

yield procedure {:layer 1}
Main({:linear_in} ps: Set perm)
refines MAIN;
requires call YieldInit(ps);
{
  var {:pending_async}{:layer 1} Broadcast_PAs:[BROADCAST]int;
  var {:pending_async}{:layer 1} Collect_PAs:[COLLECT]int;
  var i:pid;
  var {:linear} s: One perm;
  var {:linear} r: One perm;
  var {:linear} ps': Set perm;

  ps' := ps;
  i := 1;
  while (i <= n)
  invariant {:layer 1} 1 <= i && i <= n + 1;
  invariant {:layer 1} ps'->val == (lambda p:perm :: pid(p->i) && p->i >= i);
  invariant {:layer 1} Broadcast_PAs == ToMultiset(InitialBroadcastPAs(i));
  invariant {:layer 1} Collect_PAs == ToMultiset(InitialCollectPAs(i));
  {
    call s := One_Get(ps', Broadcast(i));
    call r := One_Get(ps', Collect(i));
    async call Broadcast(s, i);
    async call Collect(r, i);
    i := i + 1;
  }
  assert {:layer 1} Broadcast_PAs == ToMultiset(AllBroadcasts());
  assert {:layer 1} Collect_PAs == ToMultiset(AllCollects());
}

yield procedure {:layer 1} Broadcast({:linear_in} p: One perm, i:pid)
refines BROADCAST;
requires {:layer 1} pid(i) && p->val == Broadcast(i);
{
  var j: pid;
  var v: val;
  var {:layer 1} old_CH_low: [pid][val]int;

  call {:layer 1} old_CH_low := Copy(CH_low);
  call v := get_value(i);
  j := 1;
  while (j <= n)
  invariant {:layer 1} 1 <= j && j <= n+1;
  invariant {:layer 1} CH_low == (lambda jj: pid :: (if pid(jj) && jj < j then MultisetPlus(old_CH_low[jj], MultisetSingleton(value[p->val->i])) else old_CH_low[jj]));
  {
    call send(v, j);
    j := j + 1;
  }
  call {:layer 1} CH := add_to_multiset(CH, value[i]);
}

yield procedure {:layer 1}
Collect({:linear_in} p: One perm, i:pid)
refines COLLECT;
requires call YieldInv();
requires {:layer 1} pid(i) && p->val == Collect(i);
{
  var j: pid;
  var d: val;
  var v: val;
  var {:layer 1} received_values: [val]int;
  var {:layer 1} old_CH_low: [pid][val]int;

  call {:layer 1} old_CH_low := Copy(CH_low);
  call d := receive(i);
  received_values := MultisetSingleton(d);
  j := 2;
  while (j <= n)
  invariant {:layer 1} 2 <= j && j <= n + 1;
  invariant {:layer 1} card(received_values) == j - 1;
  invariant {:layer 1} MultisetSubsetEq(MultisetEmpty, received_values);
  invariant {:layer 1} MultisetSubsetEq(received_values, old_CH_low[i]);
  invariant {:layer 1} CH_low == old_CH_low[i := MapSub(old_CH_low[i], received_values)];
  invariant {:layer 1} d == max(received_values);
  {
    call v := receive(i);
    if (v > d) { d := v; }
    received_values[v] := received_values[v] + 1;
    j := j + 1;
  }
  call set_decision(p, d);
}

////////////////////////////////////////////////////////////////////////////////

both action {:layer 1} GET_VALUE(i:pid) returns (v:val)
{
  v := value[i];
}

both action {:layer 1} SET_DECISION({:linear_in} p: One perm, d:val)
modifies decision;
{
  assert p->val is Collect;
  decision[p->val->i] := d;
}

left action {:layer 1} SEND(v:val, i:pid)
modifies CH_low;
{
  CH_low[i][v] := CH_low[i][v] + 1;
}

right action {:layer 1} RECEIVE(i:pid) returns (v:val)
modifies CH_low;
{
  assume CH_low[i][v] > 0;
  CH_low[i][v] := CH_low[i][v] - 1;
}

yield procedure {:layer 0} get_value(i:pid) returns (v:val);
refines GET_VALUE;

yield procedure {:layer 0} set_decision({:linear_in} p: One perm, d:val);
refines SET_DECISION;

yield procedure {:layer 0} send(v:val, i:pid);
refines SEND;

yield procedure {:layer 0} receive(i:pid) returns (v:val);
refines RECEIVE;

////////////////////////////////////////////////////////////////////////////////

const MultisetEmpty:[val]int;
axiom MultisetEmpty == MapConst(0);

function {:inline} MultisetSingleton(v:val) : [val]int
{
  MultisetEmpty[v := 1]
}

function {:inline} MultisetSubsetEq(a:[val]int, b:[val]int) : bool
{
  MapLe(a, b) == MapConst(true)
}

function {:inline} MultisetPlus(a:[val]int, b:[val]int) : [val]int
{
  MapAdd(a, b)
}

function {:inline} MultisetMinus(a:[val]int, b:[val]int) : [val]int
{
  MapSub(a, b)
}
