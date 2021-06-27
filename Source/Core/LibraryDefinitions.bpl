/// maps
function {:builtin "MapConst"} MapConst<T,U>(U): [T]U;
function {:builtin "MapEq"} MapEq<T,U>([T]U, [T]U) : [T]bool;
function {:builtin "MapIte"} MapIte<T,U>([T]bool, [T]U, [T]U) : [T]U;

function {:builtin "MapOr"} MapOr<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapAnd"} MapAnd<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapNot"} MapNot<T>([T]bool) : [T]bool;
function {:builtin "MapImp"} MapImp<T>([T]bool, [T]bool) : [T]bool;
function {:builtin "MapIff"} MapIff<T>([T]bool, [T]bool) : [T]bool;
function {:inline} MapDiff<T>(a: [T]bool, b: [T]bool) : [T]bool
{
  MapAnd(a, MapNot(b))
}

function {:builtin "MapAdd"} MapAdd<T>([T]int, [T]int) : [T]int;
function {:builtin "MapSub"} MapSub<T>([T]int, [T]int) : [T]int;
function {:builtin "MapMul"} MapMul<T>([T]int, [T]int) : [T]int;
function {:builtin "MapDiv"} MapDiv<T>([T]int, [T]int) : [T]int;
function {:builtin "MapMod"} MapMod<T>([T]int, [T]int) : [T]int;
function {:builtin "MapGt"} MapGt<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapGe"} MapGe<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapLt"} MapLt<T>([T]int, [T]int) : [T]bool;
function {:builtin "MapLe"} MapLe<T>([T]int, [T]int) : [T]bool;

function {:inline} MapUnit<T>(t: T): [T]bool
{
  MapConst(false)[t := true]
}

function {:inline} Id<T>(t: T): T
{
  t
}

function Default<T>(): T;

/// vectors
type {:datatype} Vec _;
function {:constructor} Vec<T>(contents: [int]T, len: int): Vec T;

const Identity: [int]int;
axiom (forall x: int :: Identity[x] == x);

function {:inline} AtLeast(x: int): [int]bool
{
  MapLe(MapConst(x), Identity)
}
function {:inline} Range(from: int, n: int): [int]bool {
  MapDiff(AtLeast(from), AtLeast(from + n))
}

axiom {:ctor "Vec"} (forall<T> x: Vec T :: {len#Vec(x)}{contents#Vec(x)} MapIte(Range(0, len#Vec(x)), MapConst(Default()), contents#Vec(x)) == MapConst(Default()));
axiom {:ctor "Vec"} (forall<T> x: Vec T :: {len#Vec(x)} len#Vec(x) >= 0);

function {:inline} Vec_Empty<T>(): Vec T
{
  Vec(MapConst(Default()), 0)
}
function {:inline} Vec_Append<T>(v: Vec T, x: T) : Vec T
{
  Vec(contents#Vec(v)[len#Vec(v) := x], len#Vec(v) + 1)
}
function {:inline} Vec_Update<T>(v: Vec T, i: int, x: T) : Vec T
{
  if (0 <= i && i < len#Vec(v)) then Vec(contents#Vec(v)[i := x], len#Vec(v)) else v
}
function {:inline} Vec_Nth<T>(v: Vec T, i: int): T
{
  contents#Vec(v)[i]
}
function {:inline} Vec_Len<T>(v: Vec T): int
{
  len#Vec(v)
}

function {:inline} Vec_Concat<T>(v1: Vec T, v2: Vec T): Vec T {
    Vec(
        (lambda {:pool "Concat"} i: int ::
            if (i < 0) then Default()
            else if (0 <= i && i < Vec_Len(v1)) then Vec_Nth(v1, i)
            else if (Vec_Len(v1) <= i && i < Vec_Len(v1) + Vec_Len(v2)) then Vec_Nth(v2, i - Vec_Len(v1))
            else Default()),
        Vec_Len(v1) + Vec_Len(v2)
        )
}

function {:inline} Vec_Slice<T>(v: Vec T, i: int, j: int): Vec T {
    if (0 <= i && i < j && j <= len#Vec(v)) then
        Vec(
            (lambda {:pool "Slice"} k: int ::
                if (k < 0) then Default()
                else if (0 <= k && k < j - i) then Vec_Nth(v, k + i)
                else Default()),
            j - i
            )
    else Vec_Empty()
}

function {:inline} Vec_Swap<T>(v: Vec T, i: int, j: int): Vec T {
    if (0 <= i && i < len#Vec(v) && 0 <= j && j < len#Vec(v) && i != j)
    then Vec(contents#Vec(v)[i := contents#Vec(v)[j]][j := contents#Vec(v)[i]], len#Vec(v))
    else v
}

function {:inline} Vec_Remove<T>(v: Vec T): Vec T {
    if (0 < len#Vec(v))
    then Vec(contents#Vec(v)[len#Vec(v)-1 := Default()], len#Vec(v) - 1)
    else Vec_Empty()
}

// extensionality lemma to be used explicitly by the programmer
procedure Vec_Ext<T>(A: Vec T, B: Vec T) returns (i: int);
ensures A == B || Vec_Len(A) != Vec_Len(B) || Vec_Nth(A, i) != Vec_Nth(B, i);

/// sequences
type {:builtin "Seq"} Seq _;
function {:builtin "seq.empty"} Seq_Empty<T>(): Seq T;
function {:builtin "seq.len"} Seq_Len<T>(a: Seq T): int;
function {:builtin "seq.++"} Seq_Concat<T>(a: Seq T, b: Seq T): Seq T;
function {:builtin "seq.unit"} Seq_Unit<T>(v: T): Seq T;
function {:builtin "seq.nth"} Seq_Nth<T>(a: Seq T, i: int): T;
function {:builtin "seq.extract"} Seq_Extract<T>(a: Seq T, pos: int, length: int): Seq T;
