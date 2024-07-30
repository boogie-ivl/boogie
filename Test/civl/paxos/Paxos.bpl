////////////////////////////////////////////////////////////////////////////////
//// Types and constants
const numNodes: int;
axiom numNodes > 0;

type Round = int;
function Round(x: int): bool { 1 <= x }

type Node = int;
function Node(x: int): bool { 1 <= x && x <= numNodes }

type NodeSet = [Node]bool;

type Value;

datatype VoteInfo { VoteInfo(value: Value, ns: NodeSet) }

/* 0 <= lastVoteRound, lastJoinRound <= numRounds */
datatype AcceptorState { AcceptorState(lastJoinRound: Round, lastVoteRound: int, lastVoteValue: Value) }

/* 0 <= lastVoteRound <= numRounds */
datatype JoinResponse { JoinResponse(from: Node, lastVoteRound: int, lastVoteValue: Value) }
type JoinResponseChannel = Map Permission JoinResponse;

datatype VoteResponse { VoteResponse(from: Node) }
type VoteResponseChannel = Map Permission VoteResponse;

datatype Permission {
  JoinPerm(r:Round, n: Node),
  VotePerm(r:Round, n: Node),
  ConcludePerm(r: Round)
}

////////////////////////////////////////////////////////////////////////////////
//// Functions

function {:inline} NoNodes(): NodeSet { MapConst(false) }
function {:inline} SingletonNode(node: Node): NodeSet { NoNodes()[node := true] }

function Cardinality(q: NodeSet): int;
axiom Cardinality(NoNodes()) == 0;

function IsQuorum(ns: NodeSet): bool {
  2 * Cardinality(ns) > numNodes &&
  (forall n: Node :: ns[n] ==> Node(n))
}

axiom (forall ns1: NodeSet, ns2: NodeSet ::
  IsQuorum(ns1) && IsQuorum(ns2) ==> (exists n: Node :: Node(n) && ns1[n] && ns2[n])
);

// MaxRound(r, ns, voteInfo) returns the highest round less than r that some node in ns voted for.
// If no node in ns has voted for a round less than r, then it returns 0.
function MaxRound(r: Round, ns: NodeSet, voteInfo: [Round]Option VoteInfo): int;
axiom (forall r: Round, ns: NodeSet, voteInfo: [Round]Option VoteInfo ::
  Round(r) ==>
  (
    var ret := MaxRound(r, ns, voteInfo);
    0 <= ret && ret < r &&
    (forall r': Round :: ret < r' && r' < r && voteInfo[r'] is Some ==> IsDisjoint(ns, voteInfo[r']->t->ns)) &&
    (Round(ret) ==> voteInfo[ret] is Some && !IsDisjoint(ns, voteInfo[ret]->t->ns))
  )
);

function {:inline} AllPermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p->r == r))
}

function {:inline} JoinPermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p is JoinPerm && p->r == r))
}

function {:inline} VotePermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} p is VotePerm && p->r == r))
}

function {:inline} ProposePermissions(r: Round) : Set Permission
{
  Set((lambda {:pool "Permission"} p:Permission :: {:add_to_pool "Permission", p} !(p is JoinPerm) && p->r == r))
}

function {:inline} JoinPAs(r: Round) : [A_Join]bool
{
  (lambda pa: A_Join :: pa->r == r && Node(pa->n) && pa->p->val == JoinPerm(r, pa->n))
}

function {:inline} VotePAs(r: Round, v: Value) : [A_Vote]bool
{
  (lambda pa: A_Vote :: pa->r == r && Node(pa->n) && pa->v == v && pa->p->val == VotePerm(r, pa->n))
}

////////////////////////////////////////////////////////////////////////////////
//// Global variables
// Abstract
var {:layer 1,2} joinedNodes: [Round]NodeSet;
var {:layer 1,2} voteInfo: [Round]Option VoteInfo;
var {:layer 1,3} decision: [Round]Option Value; // spec

// Concrete
var {:layer 0,1} acceptorState: [Node]AcceptorState;
var {:layer 0,1} joinChannel: [Round][JoinResponse]int;
var {:layer 0,1} voteChannel: [Round][VoteResponse]int;

// Intermediate channel representation
var {:layer 1,1} {:linear} permJoinChannel: JoinResponseChannel;
var {:layer 1,1} {:linear} permVoteChannel: VoteResponseChannel;

////////////////////////////////////////////////////////////////////////////////

function {:inline} Init (
  ps: Set Permission, decision: [Round]Option Value) : bool
{
  ps->val == (lambda p: Permission :: true) &&
  decision == (lambda r: Round :: None())
}

function {:inline} InitLow (
  acceptorState: [Node]AcceptorState,
  joinChannel: [Round][JoinResponse]int,
  voteChannel: [Round][VoteResponse]int,
  permJoinChannel: JoinResponseChannel,
  permVoteChannel: VoteResponseChannel) : bool
{
  (forall n: Node :: acceptorState[n]->lastJoinRound == 0 && acceptorState[n]->lastVoteRound == 0) &&
  (forall r: Round, jr: JoinResponse :: joinChannel[r][jr] == 0) &&
  (forall r: Round, vr: VoteResponse :: voteChannel[r][vr] == 0) &&
  permJoinChannel == Map_Empty() &&
  permVoteChannel == Map_Empty()
}
