atomic action {:layer 2} A_Paxos({:linear_in} ps: Set Permission)
modifies joinedNodes, voteInfo, decision;
refines A_Paxos' using INV;
creates A_StartRound;
{
  var {:pool "NumRounds"} numRounds: int;
  assert Init(ps, decision);
  assume
    {:add_to_pool "Round", 0, numRounds}
    {:add_to_pool "NumRounds", numRounds}
    0 <= numRounds;
  joinedNodes := (lambda r: Round:: NoNodes());
  voteInfo := (lambda r: Round:: None());
  call {:linear ps} create_asyncs((lambda pa: A_StartRound :: AllPermissions(pa->r) == pa->r_lin && Round(pa->r) && pa->r <= numRounds));
}

atomic action {:layer 3} A_Paxos'({:linear_in} ps: Set Permission)
modifies decision;
{
  assert Init(ps, decision);
  havoc decision;
  assume (forall r1: Round, r2: Round :: decision[r1] is Some && decision[r2] is Some ==> decision[r1] == decision[r2]);
}

action {:layer 2}
INV({:linear_in} ps: Set Permission)
creates A_StartRound, A_Propose, A_Conclude, A_Join, A_Vote;
modifies joinedNodes, voteInfo, decision;
asserts Init(ps, decision);
{
  var {:linear} ps': Set Permission;
  var {:linear} proposePermissions: Set Permission;
  var {:linear} joinPermissions: Set Permission;
  var {:linear} votePermissions: Set Permission;
  var {:linear} concludePermission: One Permission;
  var {:pool "NumRounds"} numRounds: int;
  var {:pool "Round"} k: int;
  var {:pool "Node"} m: Node;

  ps' := ps;
  havoc joinedNodes, voteInfo, decision;

  // This invariant is the "pending async skeleton" which states the possible
  // pending asyncs in the sequentialization. The existentially quantified k
  // denotes the number of rounds that already finished (i.e., rounds 1 to k
  // finished and k+1 is the round that currently executes), and similarly the
  // existentially quantified m denotes the number of nodes that already
  // finished in the current round.

  assume
    {:add_to_pool "NumRounds", numRounds}
    {:add_to_pool "Round", k, k+1, numRounds}
    0 <= k && k <= numRounds;

  if (k == numRounds) {
      // do nothing
  } else if (*) {
      assume
        (forall r: Round :: r < 1 || r > k ==> voteInfo[r] is None) &&
        (forall r: Round :: r < 1 || r > k ==> decision[r] is None);
      call {:linear ps'} create_asyncs((lambda {:pool "A_StartRound"} pa: A_StartRound :: AllPermissions(pa->r) == pa->r_lin && k < pa->r && pa->r <= numRounds));
      call set_choice(A_StartRound(k+1, AllPermissions(k+1)));
  } else if (*) {
      assume
        (forall r: Round :: r < 1 || r > k ==> voteInfo[r] is None) &&
        (forall r: Round :: r < 1 || r > k ==> decision[r] is None);
      assume
        {:add_to_pool "Node", m}
        {:add_to_pool "A_Join", A_Join(k+1, numNodes, One(JoinPerm(k+1, numNodes)))}
        0 <= m && m <= numNodes;
      call proposePermissions := Set_Get(ps', ProposePermissions(k+1)->val);
      async call A_Propose(k+1, proposePermissions);
      call joinPermissions := Set_Get(ps', JoinPermissions(k+1)->val);
      call {:linear joinPermissions} create_asyncs((lambda {:pool "A_Join"} pa: A_Join :: pa->r == k+1 && m < pa->n && pa->n <= numNodes && pa->p->val == JoinPerm(k+1, pa->n)));
      call {:linear ps'} create_asyncs((lambda pa: A_StartRound :: AllPermissions(pa->r) == pa->r_lin && k+1 < pa->r && pa->r <= numRounds));
      if (m == numNodes) {
        call set_choice(A_Propose(k+1, ProposePermissions(k+1)));
      } else {
        call set_choice(A_Join(k+1, m+1, One(JoinPerm(k+1, m+1))));
      }
  } else {
      assume
        voteInfo[k+1] is Some &&
        (forall r: Round :: r < 1 || r > k+1 ==> voteInfo[r] is None) &&
        (forall r: Round :: r < 1 || r > k ==> decision[r] is None);
      assume
        {:add_to_pool "Node", m}
        {:add_to_pool "A_Vote", A_Vote(k+1, numNodes, voteInfo[k+1]->t->value, One(VotePerm(k+1, numNodes)))}
        {:add_to_pool "A_StartRound", A_StartRound(numRounds, AllPermissions(numRounds))}
        0 <= m && m <= numNodes &&
        (forall n: Node :: n < 1 || n > m ==> !voteInfo[k+1]->t->ns[n]);
      call concludePermission := One_Get(ps', ConcludePerm(k+1));
      async call A_Conclude(k+1, voteInfo[k+1]->t->value, concludePermission);
      call votePermissions := Set_Get(ps', VotePermissions(k+1)->val);
      call {:linear votePermissions} create_asyncs((lambda {:pool "A_Vote"} pa: A_Vote :: pa->r == k+1 && m < pa->n && pa->n <= numNodes && pa->v == voteInfo[k+1]->t->value && pa->p->val == VotePerm(k+1, pa->n)));
      call {:linear ps'} create_asyncs((lambda {:pool "A_StartRound"} pa: A_StartRound :: AllPermissions(pa->r) == pa->r_lin && k+1 < pa->r && pa->r <= numRounds));
      if (m == numNodes) {
        call set_choice(A_Conclude(k+1, voteInfo[k+1]->t->value, One(ConcludePerm(k+1))));
      } else {
        call set_choice(A_Vote(k+1, m+1, voteInfo[k+1]->t->value, One(VotePerm(k+1, m+1))));
      }
  }

  // If there was a decision for some value, then there must have been a
  // proposal of the same value and a quorum of nodes that voted for it.
  assume (forall r: Round :: decision[r] is Some ==>
    voteInfo[r] is Some &&
    voteInfo[r]->t->value == decision[r]->t &&
    (exists q: NodeSet ::
      IsSubset(q, voteInfo[r]->t->ns) && IsQuorum(q)));

  // This is the main invariant to prove
  assume (forall r1: Round, r2: Round :: decision[r1] is Some && r1 <= r2 && voteInfo[r2] is Some ==> voteInfo[r2]->t->value == decision[r1]->t);

  // This is the main property to prove
  assume (forall r1: Round, r2: Round :: decision[r1] is Some && decision[r2] is Some ==> decision[r1] == decision[r2]);
}

// Local Variables:
// flycheck-disabled-checkers: (boogie)
// End:
