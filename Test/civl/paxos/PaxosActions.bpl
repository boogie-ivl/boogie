async atomic action {:layer 2} A_StartRound(r: Round, {:linear_in} r_lin: Set Permission)
creates A_Join, A_Propose;
asserts AllPermissions(r) == r_lin;
asserts Round(r);
{
  var {:linear} r_lin': Set Permission;
  var {:linear} joinPermissions: Set Permission;

  assume
    {:add_to_pool "Round", r-1}
    {:add_to_pool "Node", 0}
    {:add_to_pool "Permission", ConcludePerm(r)}
    true;

  r_lin' := r_lin;
  call joinPermissions := Set_Get(r_lin', JoinPermissions(r)->val);
  call {:linear joinPermissions} create_asyncs(JoinPAs(r));
  async call A_Propose(r, r_lin');
}

async atomic action {:layer 2} A_Propose(r: Round, {:linear_in} ps: Set Permission)
creates A_Vote, A_Conclude;
modifies voteInfo;
asserts Round(r);
asserts ps == ProposePermissions(r);
asserts voteInfo[r] is None;
{
  var {:linear} ps': Set Permission;
  var {:linear} concludePermission: One Permission;
  var {:pool "Round"} maxRound: int;
  var {:pool "MaxValue"} maxValue: Value;
  var {:pool "NodeSet"} ns: NodeSet;

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", 0}
    {:add_to_pool "NodeSet", ns}
    {:add_to_pool "Permission", ConcludePerm(r)}
    {:add_to_pool "MaxValue", maxValue}
    true;

  if (*) {
    assume IsSubset(ns, joinedNodes[r]) && IsQuorum(ns);
    maxRound := MaxRound(r, ns, voteInfo);
    if (maxRound != 0)
    {
      maxValue := voteInfo[maxRound]->t->value;
    }
    voteInfo[r] := Some(VoteInfo(maxValue, NoNodes()));
    ps' := ps;
    call concludePermission := One_Get(ps', ConcludePerm(r));
    async call A_Conclude(r, maxValue, concludePermission);
    call {:linear ps'} create_asyncs(VotePAs(r, maxValue));
  }
}

async atomic action {:layer 2} A_Conclude(r: Round, v: Value, {:linear_in} p: One Permission)
modifies decision;
{
  var {:pool "NodeSet"} q: NodeSet;

  assert Round(r);
  assert p->val == ConcludePerm(r);
  assert voteInfo[r] is Some;
  assert voteInfo[r]->t->value == v;

  assume {:add_to_pool "Round", r} {:add_to_pool "NodeSet", q} true;

  if (*) {
    assume IsSubset(q, voteInfo[r]->t->ns) && IsQuorum(q);
    decision[r] := Some(v);
  }
}

async atomic action {:layer 2} A_Join(r: Round, n: Node, {:linear_in} p: One Permission)
modifies joinedNodes;
{
  assert Round(r);
  assert p->val == JoinPerm(r, n);

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' < r);
    joinedNodes[r][n] := true;
  }
}

async atomic action {:layer 2} A_Vote(r: Round, n: Node, v: Value, {:linear_in} p: One Permission)
modifies joinedNodes, voteInfo;
{
  assert Round(r);
  assert p->val == VotePerm(r, n);
  assert voteInfo[r] is Some;
  assert voteInfo[r]->t->value == v;
  assert !voteInfo[r]->t->ns[n];

  assume
    {:add_to_pool "Round", r, r-1}
    {:add_to_pool "Node", n}
    true;

  if (*) {
    assume (forall r': Round :: Round(r') && joinedNodes[r'][n] ==> r' <= r);
    voteInfo[r] := Some(VoteInfo(v, voteInfo[r]->t->ns[n := true]));
    joinedNodes[r][n] := true;
  }
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
