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
