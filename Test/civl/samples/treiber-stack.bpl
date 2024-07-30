// RUN: %parallel-boogie -lib:base -lib:node -vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype LocPiece { Left(), Right() }
function {:inline} AllLocPieces(): Set LocPiece {
  Set_Add(Set_Add(Set_Empty(), Left()), Right())
}

type TreiberNode _;
type LocTreiberNode T = Fraction (Loc (TreiberNode T)) LocPiece;
type StackElem T = Node (LocTreiberNode T) T;
type StackMap T = Map (LocTreiberNode T) (StackElem T);
datatype Treiber<T> { Treiber(top: Option (LocTreiberNode T), {:linear} stack: StackMap T) }

type X; // module type parameter

var {:layer 4, 5} Stack: Map (Loc (Treiber X)) (Vec X);
var {:layer 0, 4} {:linear} ts: Map (Loc (Treiber X)) (Treiber X);

/// Yield invariants

function {:inline} Domain(ts: Map (Loc (Treiber X)) (Treiber X), loc_t: Loc (Treiber X)): Set (LocTreiberNode X) {
  ts->val[loc_t]->stack->dom
}

yield invariant {:layer 1} Yield();

yield invariant {:layer 2} TopInStack(loc_t: Loc (Treiber X));
invariant Map_Contains(ts, loc_t);
invariant (var loc_n := Map_At(ts, loc_t)->top; loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t));
invariant (forall loc_n: LocTreiberNode X :: Set_Contains(Domain(ts, loc_t), loc_n) ==> 
              (var loc_n' := Map_At(Map_At(ts, loc_t)->stack, loc_n)->next; loc_n' is None || Set_Contains(Domain(ts, loc_t), loc_n'->t)));

yield invariant {:layer 2} LocInStackOrNone(loc_t: Loc (Treiber X), loc_n: Option (LocTreiberNode X));
invariant Map_Contains(ts, loc_t);
invariant loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t);

yield invariant {:layer 3} LocInStack(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X);
invariant Map_Contains(ts, loc_t);
invariant Set_Contains(Domain(ts, loc_t), loc_n);

yield invariant {:layer 4} ReachInStack(loc_t: Loc (Treiber X));
invariant Map_Contains(ts, loc_t);
invariant (var t := ts->val[loc_t]; Between(t->stack->val, t->top, t->top, None()));
invariant (var t := ts->val[loc_t]; IsSubset(BetweenSet(t->stack->val, t->top, None()), Domain(ts, loc_t)->val));
invariant (var loc_n := Map_At(ts, loc_t)->top; loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t));
invariant (forall {:pool "A"} loc_n: LocTreiberNode X :: {:add_to_pool "A", loc_n} Set_Contains(Domain(ts, loc_t), loc_n) ==>
              loc_n == Fraction(loc_n->val, Left(), AllLocPieces()) &&
              (var loc_n' := Map_At(Map_At(ts, loc_t)->stack, loc_n)->next; loc_n' is None || Set_Contains(Domain(ts, loc_t), loc_n'->t)));
invariant Map_At(Stack, loc_t) == Abs(Map_At(ts, loc_t));

yield invariant {:layer 4} StackDom();
invariant Stack->dom == ts->dom;

yield invariant {:layer 4} PushLocInStack(
  loc_t: Loc (Treiber X), node: StackElem X, new_loc_n: LocTreiberNode X, {:linear} right_loc_piece: One (LocTreiberNode X));
invariant Map_Contains(ts, loc_t);
invariant Set_Contains(Domain(ts, loc_t), new_loc_n);
invariant right_loc_piece->val == Fraction(new_loc_n->val, Right(), AllLocPieces());
invariant new_loc_n == Fraction(new_loc_n->val, Left(), AllLocPieces());
invariant (var t := ts->val[loc_t]; Map_At(t->stack, new_loc_n) == node && !BetweenSet(t->stack->val, t->top, None())[new_loc_n]);

/// Layered implementation

atomic action {:layer 5} AtomicAlloc() returns (loc_t: Loc (Treiber X))
modifies Stack;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));

  call one_loc_t := One_New();
  loc_t := one_loc_t->val;
  assume !Map_Contains(Stack, loc_t);
  Stack := Map_Update(Stack, loc_t, Vec_Empty());
}
yield procedure {:layer 4} Alloc() returns (loc_t: Loc (Treiber X))
refines AtomicAlloc;
preserves call StackDom();
{
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} treiber: Treiber X;
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  top := None();
  call stack := Map_MakeEmpty();
  treiber := Treiber(top, stack);
  call one_loc_t := One_New();
  call cell_t := Cell_Pack(one_loc_t, treiber);
  loc_t := one_loc_t->val;
  call AllocTreiber#0(cell_t);
  call {:layer 4} Stack := Copy(Map_Update(Stack, loc_t, Vec_Empty()));
  call {:layer 4} AbsLemma(treiber);
}

atomic action {:layer 5} AtomicPush(loc_t: Loc (Treiber X), x: X) returns (success: bool)
modifies Stack;
{
  if (*) {
    Stack := Map_Update(Stack, loc_t, Vec_Append(Map_At(Stack, loc_t), x));
    success := true;
  } else {
    success := false;
  }
}
yield procedure {:layer 4} Push(loc_t: Loc (Treiber X), x: X) returns (success: bool)
refines AtomicPush;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  var loc_n: Option (LocTreiberNode X);
  var new_loc_n: LocTreiberNode X;
  var {:linear} right_loc_piece: One (LocTreiberNode X);
  var {:layer 4} old_treiber: Treiber X;

  call {:layer 4} old_treiber := Copy(ts->val[loc_t]);
  call loc_n, new_loc_n, right_loc_piece := AllocNode#3(loc_t, x);
  call {:layer 4} FrameLemma(old_treiber, ts->val[loc_t]);
  par ReachInStack(loc_t) | StackDom() | PushLocInStack(loc_t, Node(loc_n, x), new_loc_n, right_loc_piece);
  call success := WriteTopOfStack#0(loc_t, loc_n, Some(new_loc_n));
  if (success) {
    call {:layer 4} Stack := Copy(Map_Update(Stack, loc_t, Vec_Append(Map_At(Stack, loc_t), x)));
    assert {:layer 4} ts->val[loc_t]->top != None();
    call {:layer 4} AbsLemma(ts->val[loc_t]);
  }
}

atomic action {:layer 5} AtomicPop(loc_t: Loc (Treiber X)) returns (success: bool, x_opt: Option X)
modifies Stack;
{
  var stack: Vec X;

  if (*) {
    stack := Map_At(Stack, loc_t);
    if (Vec_Len(stack) > 0) {
      x_opt := Some(Vec_Nth(stack, Vec_Len(stack) - 1));
      Stack := Map_Update(Stack, loc_t, Vec_Remove(stack));
    } else {
      x_opt := None();
    }
    success := true;
  } else {
    success := false;
    x_opt := None();
  }
}
yield procedure {:layer 4} Pop(loc_t: Loc (Treiber X)) returns (success: bool, x_opt: Option X)
refines AtomicPop;
preserves call TopInStack(loc_t);
preserves call ReachInStack(loc_t);
preserves call StackDom();
{
  call {:layer 4} AbsLemma(ts->val[loc_t]);
  call success, x_opt := PopIntermediate(loc_t);
  if (x_opt is Some) {
    assert {:layer 4} Vec_Len(Map_At(Stack, loc_t)) > 0;
    call {:layer 4} Stack := Copy(Map_Update(Stack, loc_t, Vec_Remove(Map_At(Stack, loc_t))));
  }
}

atomic action {:layer 4} AtomicAllocNode#3(loc_t: Loc (Treiber X), x: X)
  returns (loc_n: Option (LocTreiberNode X), new_loc_n: LocTreiberNode X, {:linear} right_loc_piece: One (LocTreiberNode X))
modifies ts;
asserts Map_Contains(ts, loc_t);
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One (Loc (TreiberNode X));
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var {:linear} loc_pieces: Set (Fraction (Loc (TreiberNode X)) LocPiece);
  var {:linear} left_loc_piece: One (Fraction (Loc (TreiberNode X)) LocPiece);
  
  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  Treiber(top, stack) := treiber;
  assume loc_n is None || Map_Contains(stack, loc_n->t);
  call one_loc_n := One_New();
  call loc_pieces := One_To_Fractions(one_loc_n, AllLocPieces());
  call left_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Left(), AllLocPieces()));
  new_loc_n := left_loc_piece->val;
  call right_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Right(), AllLocPieces()));
  call cell_n := Cell_Pack(left_loc_piece, Node(loc_n, x));
  call Map_Put(stack, cell_n);
  treiber := Treiber(top, stack);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 3} AllocNode#3(loc_t: Loc (Treiber X), x: X)
  returns (loc_n: Option (LocTreiberNode X), new_loc_n: LocTreiberNode X, {:linear} right_loc_piece: One (LocTreiberNode X))
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, Some(new_loc_n));
refines AtomicAllocNode#3;
{
  var {:linear} one_loc_n: One (Loc (TreiberNode X));
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);
  var {:linear} loc_pieces: Set (Fraction (Loc (TreiberNode X)) LocPiece);
  var {:linear} left_loc_piece: One (Fraction (Loc (TreiberNode X)) LocPiece);

  call loc_n := ReadTopOfStack#Push(loc_t);
  call one_loc_n := One_New();
  call loc_pieces := One_To_Fractions(one_loc_n, AllLocPieces());
  call left_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Left(), AllLocPieces()));
  new_loc_n := left_loc_piece->val;
  call right_loc_piece := One_Get(loc_pieces, Fraction(one_loc_n->val, Right(), AllLocPieces()));
  call cell_n := Cell_Pack(left_loc_piece, Node(loc_n, x));
  call AllocNode#0(loc_t, cell_n);
}

atomic action {:layer 4} AtomicPopIntermediate(loc_t: Loc (Treiber X)) returns (success: bool, x_opt: Option X)
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var loc_n: Option (LocTreiberNode X);
  var {:linear} treiber: Treiber X;
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var x: X;

  assert Map_Contains(ts, loc_t);
  if (*) {
    call cell_t := Map_Get(ts, loc_t);
    call one_loc_t, treiber := Cell_Unpack(cell_t);
    Treiber(top, stack) := treiber;
    assume top is Some && Map_Contains(stack, top->t);
    Node(loc_n, x) := Map_At(stack, top->t);
    treiber := Treiber(loc_n, stack);
    call cell_t := Cell_Pack(one_loc_t, treiber);
    call Map_Put(ts, cell_t);
    x_opt := Some(x);
    success := true;
  }
  else if (*) {
    assume Map_At(ts, loc_t)->top is None;
    x_opt := None();
    success := true;
  } else {
    x_opt := None();
    success := false;
  }
}
yield procedure {:layer 3} PopIntermediate(loc_t: Loc (Treiber X)) returns (success: bool, x_opt: Option X)
refines AtomicPopIntermediate;
preserves call TopInStack(loc_t);
{
  var loc_n, new_loc_n: Option (LocTreiberNode X);
  var node: StackElem X;
  var x: X;

  call loc_n := ReadTopOfStack#Pop(loc_t);
  if (loc_n == None()) {
    x_opt := None();
    success := true;
    return;
  }
  par LocInStack(loc_t, loc_n->t) | LocInStackOrNone(loc_t, loc_n) | TopInStack(loc_t);
  call node := LoadNode#0(loc_t, loc_n->t);
  call Yield();
  Node(new_loc_n, x) := node;
  call success := WriteTopOfStack#0(loc_t, loc_n, new_loc_n);
  if (success) {
    x_opt := Some(x);
  } else {
    x_opt := None();
  }
}

right action {:layer 3} AtomicReadTopOfStack#Push(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
{
  assert Map_Contains(ts, loc_t);
  assume loc_n is None || Set_Contains(Domain(ts, loc_t), loc_n->t);
}
yield procedure {:layer 2} ReadTopOfStack#Push(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, loc_n);
refines AtomicReadTopOfStack#Push;
{
  call loc_n := ReadTopOfStack#0(loc_t);
}

atomic action {:layer 3} AtomicReadTopOfStack#Pop(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
{
  assert Map_Contains(ts, loc_t);
  assume if loc_n is None then Map_At(ts, loc_t)->top is None else Set_Contains(Domain(ts, loc_t), loc_n->t);
}
yield procedure {:layer 2} ReadTopOfStack#Pop(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
preserves call TopInStack(loc_t);
ensures call LocInStackOrNone(loc_t, loc_n);
refines AtomicReadTopOfStack#Pop;
{
  call loc_n := ReadTopOfStack#0(loc_t);
}

right action {:layer 2,3} AtomicLoadNode#1(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
{
  assert Map_Contains(ts, loc_t);
  assert Map_Contains(Map_At(ts, loc_t)->stack, loc_n);
  node := Map_At(Map_At(ts, loc_t)->stack, loc_n);
}

/// Primitives

atomic action {:layer 1} AtomicLoadNode#0(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X)
modifies ts;
refines AtomicLoadNode#1;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var top: Option (LocTreiberNode X);
  var {:linear} stack: StackMap X;
  var {:linear} one_loc_n: One (LocTreiberNode X);
  var {:linear} cell_n: Cell (LocTreiberNode X) (StackElem X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  Treiber(top, stack) := treiber;
  call cell_n := Map_Get(stack, loc_n);
  call one_loc_n, node := Cell_Unpack(cell_n);
  call cell_n := Cell_Pack(one_loc_n, node);
  call Map_Put(stack, cell_n);
  treiber := Treiber(top, stack);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} LoadNode#0(loc_t: Loc (Treiber X), loc_n: LocTreiberNode X) returns (node: StackElem X);
refines AtomicLoadNode#0;

atomic action {:layer 1,2} AtomicReadTopOfStack#0(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  loc_n := treiber->top;
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} ReadTopOfStack#0(loc_t: Loc (Treiber X)) returns (loc_n: Option (LocTreiberNode X));
refines AtomicReadTopOfStack#0;

atomic action {:layer 1,4} AtomicWriteTopOfStack#0(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (success: bool)
modifies ts;
{
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);
  var {:linear} one_loc_t: One (Loc (Treiber X));

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  if (old_loc_n == treiber->top) {
    treiber->top := new_loc_n;
    success := true;
  } else {
    success := false;
  }
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} WriteTopOfStack#0(
  loc_t: Loc (Treiber X), old_loc_n: Option (LocTreiberNode X), new_loc_n: Option (LocTreiberNode X)) returns (success: bool);
refines AtomicWriteTopOfStack#0;

atomic action {:layer 1,3} AtomicAllocNode#0(loc_t: Loc (Treiber X), {:linear_in} cell_n: Cell (LocTreiberNode X) (StackElem X))
modifies ts;
{
  var {:linear} one_loc_t: One (Loc (Treiber X));
  var {:linear} treiber: Treiber X;
  var {:linear} cell_t: Cell (Loc (Treiber X)) (Treiber X);

  call cell_t := Map_Get(ts, loc_t);
  call one_loc_t, treiber := Cell_Unpack(cell_t);
  call Map_Put(treiber->stack, cell_n);
  call cell_t := Cell_Pack(one_loc_t, treiber);
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} AllocNode#0(loc_t: Loc (Treiber X), {:linear_in} cell_n: Cell (LocTreiberNode X) (StackElem X));
refines AtomicAllocNode#0;

atomic action {:layer 1,4} AtomicAllocTreiber#0({:linear_in} cell_t: Cell (Loc (Treiber X)) (Treiber X))
modifies ts;
{
  call Map_Put(ts, cell_t);
}
yield procedure {:layer 0} AllocTreiber#0({:linear_in} cell_t: Cell (Loc (Treiber X)) (Treiber X));
refines AtomicAllocTreiber#0;

/// Proof of abstraction with a manual encoding of termination

// Abs and AbsDefinition together model the abstraction function
function Abs(treiber: Treiber X): Vec X;
function {:inline} AbsDefinition(treiber: Treiber X): Vec X {
if treiber->top == None() then
  Vec_Empty() else
  (var n := Map_At(treiber->stack, treiber->top->t);
    (var treiber' := Treiber(n->next, treiber->stack); 
      Vec_Append(Abs(treiber'), n->val)))
}

pure procedure AbsCompute(treiber: Treiber X, treiber': Treiber X) returns (absStack: Vec X)
requires treiber->top == treiber'->top;
requires IsSubset(treiber->stack->dom->val, treiber'->stack->dom->val);
requires MapIte(treiber->stack->dom->val, treiber->stack->val, MapConst(Default())) ==
         MapIte(treiber->stack->dom->val, treiber'->stack->val, MapConst(Default()));
requires Between(treiber->stack->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->stack->val, treiber->top, None()), treiber->stack->dom->val);
ensures absStack == AbsDefinition(treiber);
ensures absStack == AbsDefinition(treiber');
free ensures absStack == Abs(treiber);
free ensures absStack == Abs(treiber');
{
  var loc_n: Option (LocTreiberNode X);
  var n: StackElem X;

  if (treiber->top == None()) {
      absStack := Vec_Empty();
  } else {
      loc_n := treiber->top;
      assert Map_Contains(treiber->stack, loc_n->t);
      n := Map_At(treiber->stack, loc_n->t);
      // Use well-founded list reachability to prove that recursion will terminate:
      // treiber@caller->top --> treiber@callee->top --> None()
      assert Between(treiber->stack->val, loc_n, n->next, None());
      call absStack := AbsCompute(Treiber(n->next, treiber->stack), Treiber(n->next, treiber'->stack));
      absStack := Vec_Append(absStack, n->val);
  }
}

/// Useful lemmas obtained by wrapping AbsCompute

pure procedure AbsLemma(treiber: Treiber X)
requires Between(treiber->stack->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->stack->val, treiber->top, None()), treiber->stack->dom->val);
ensures Abs(treiber) == AbsDefinition(treiber);
{
  var absStack: Vec X;
  call absStack := AbsCompute(treiber, treiber);
}

pure procedure FrameLemma(treiber: Treiber X, treiber': Treiber X)
requires treiber->top == treiber'->top;
requires IsSubset(treiber->stack->dom->val, treiber'->stack->dom->val);
requires MapIte(treiber->stack->dom->val, treiber->stack->val, MapConst(Default())) ==
         MapIte(treiber->stack->dom->val, treiber'->stack->val, MapConst(Default()));
requires Between(treiber->stack->val, treiber->top, treiber->top, None());
requires IsSubset(BetweenSet(treiber->stack->val, treiber->top, None()), treiber->stack->dom->val);
ensures Abs(treiber) == Abs(treiber');
{
  var absStack: Vec X;
  call absStack := AbsCompute(treiber, treiber');
}
