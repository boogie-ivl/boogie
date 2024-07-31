// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid = int;
type Duration = int;
type ReqId;


datatype Vote { YES(), NO(), NULL() }

datatype Decision { COMMIT(), ABORT(), NONE() }



datatype Request { Request(id: ReqId, duration: Duration )}

type ParticipantPiece = Fraction ReqId Pid;

// 1, dur 3
// 1, dur 6 

// only reqId should be linear

const NumParticipants:int;
axiom NumParticipants > 0;

var {:layer 0,1} locked_requests: [Pid](Set Request);
var {:layer 0,1} participant_votes: [Pid][Request]Vote;
var {:layer 0,1} committed_requests: (Set Request);

// function {:inline} Init(req: Request, participant_votes: [Pid][Request]Vote) : bool
// {
// //   participant_votes == (lambda p:Pid :: (lambda r:Request  :: NULL())) 
//   (forall p: Pid :: participant_votes[p][req] == NULL())
// }

function {:inline} NoOverlap(req_set: (Set Request), d: Duration) : bool
{
    !(exists req: Request :: Set_Contains(req_set, req) && req->duration == d)
}

// yield invariant {:layer 1} YieldInit(req: Request);
// invariant Init(req, participant_votes); 

// yield invariant {:layer 2} YieldC1();
// invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));

// yield invariant {:layer 2} YieldC2();
// invariant (forall req: Request :: Set_Contains(committed_requests, req) ==> (forall pid: Pid :: participant_votes[pid][req] == YES() && Set_Contains(locked_requests[pid], req)));

// yield invariant {:layer 1} YieldC3();
// invariant !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && participant_votes[pid][req1] == YES() && participant_votes[pid][req2] == YES());

// yield invariant {:layer 1} YieldC4();
// invariant !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(locked_requests[pid], req1) && Set_Contains(locked_requests[pid], req2));

// yield invariant {:layer 1} YieldC5();
// invariant (forall pid: Pid, req: Request :: Set_Contains(locked_requests[pid], req) <==> participant_votes[pid][req] == YES());


yield invariant {:layer 1} YieldBig();
invariant (forall pid: Pid, req: Request :: Set_Contains(locked_requests[pid], req) <==> participant_votes[pid][req] == YES());
invariant !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(locked_requests[pid], req1) && Set_Contains(locked_requests[pid], req2));
// invariant !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && participant_votes[pid][req1] == YES() && participant_votes[pid][req2] == YES());
invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));
invariant !(exists req: Request, pid: Pid :: Set_Contains(committed_requests, req) && !Set_Contains(locked_requests[pid], req));

yield invariant {:layer 1} YieldTrue();
invariant true;

yield invariant {:layer 1} YieldVoting({:linear} pid: One ParticipantPiece, req: Request);
invariant !(exists req0:Request :: Set_Contains(locked_requests[pid->val->id], req0) && req0->id == req->id);
invariant participant_votes[pid->val->id][req] == NULL();

// function {:inline} Init2(pids:[Pid]bool) : bool
// {
//   pids == MapConst(true)
// }

// yield invariant {:layer 1} YieldInit2({:linear} pids: Set Pid);
// invariant Init2(pids->val);

function {:inline} ParticipantIds(): Set Pid {
    Set((lambda {:pool "P1"} x: int :: 1 <= x && x <= NumParticipants))
}

function {:inline} JParticipantIds(j: int): Set Pid {
    Set((lambda {:pool "P1"} x: int :: j <= x && x <= NumParticipants))
}

function {:inline} AllParticipantPieces(r: ReqId): Set ParticipantPiece {
    Set((lambda {:pool "P2"} x: ParticipantPiece :: x->val == r && x->ids == ParticipantIds() && Set_Contains(x->ids, x->id)))
}

function {:inline} JParticipantPieces(r: ReqId, j: int): Set ParticipantPiece {
    Set((lambda {:pool "P2"} x: ParticipantPiece :: x->val == r && x->ids == ParticipantIds() && Set_Contains(JParticipantIds(j), x->id)))
}

yield procedure {:layer 1} coordinator({:linear_in} reqId: One ReqId, duration: Duration)
// refines not_skip;
// requires call YieldInit(req);
// requires {:layer 1} (forall p: Pid :: old(participant_votes)[p][req] == NULL());
// requires call YieldInit2(pids);
requires call YieldBig();
// requires pids  == lambda .. are from 1 to n;
{
   var i: int;
   var j: int;
   var d: Decision;
   var v: Vote;
   var {:linear} pids: Set ParticipantPiece;
   var {:linear} pid: One ParticipantPiece;
   var {:linear} reqId': One ReqId;
   

   reqId' := reqId;
   d := COMMIT();
   j := 1;
   call pids := One_To_Fractions(reqId', ParticipantIds());
//    assert {:layer 1} pids == AllParticipantPieces(reqId'->val);
   while (j <= NumParticipants)
   invariant {:layer 1} 1 <= j && j <= NumParticipants + 1;
   invariant {:layer 1} pids == JParticipantPieces(reqId'->val, j);
   {
    call pid := One_Get(pids, (Fraction(reqId'->val, j, ParticipantIds())));
    async call voting0(Request(reqId'->val, duration), pid);
    j := j + 1;
   }

   call YieldBig();
   
   i := 1;
   while (i <= NumParticipants)
   {
    call v := receive_vote(i, Request(reqId'->val, duration));
    if (v == NO())
    {
    d := ABORT();
    }
    i := i + 1;
   }

   call YieldBig();

   if (d == COMMIT()) {
        // assert {:layer 1} false;
        // all participants said yes
        // locked requests of all pid have req
        // committed => locked
        // locked has no overlaps
        assume false;
        // assert {:layer 1} !(exists req1: Request :: req1->id != req->id && req1->duration == req->duration && Set_Contains(committed_requests, req1));
        call add_to_committed_requests(Request(reqId'->val, duration));
   }
}

async action {:layer 1} voting(req: Request, {:linear_in} pid: One ParticipantPiece)
modifies locked_requests, participant_votes;
// asserts !(exists req0:Request :: Set_Contains(locked_requests[pid], req0) && req0->id == req->id);
// asserts participant_votes[pid][req] == NULL();
{
    assert !(exists req0:Request :: Set_Contains(locked_requests[pid->val->id], req0) && req0->id == req->id);
    assert participant_votes[pid->val->id][req] == NULL();
    if (*) {
        participant_votes[pid->val->id][req] := NO();
        return;
    }
    else {
        if (NoOverlap(locked_requests[pid->val->id], req->duration)) {
            locked_requests[pid->val->id] := Set_Add(locked_requests[pid->val->id], req);
            participant_votes[pid->val->id][req] := YES();
        }
        else {
            participant_votes[pid->val->id][req] := NO();
        }
    }
}
yield procedure {:layer 0} voting1(req: Request, {:linear_in} pid: One ParticipantPiece);
refines voting;

yield procedure {:layer 1} voting0(req: Request, {:linear_in}  pid: One ParticipantPiece)
requires call YieldBig();
requires call YieldVoting(pid, req);
{
    // assert {:layer 1} !(exists req0:Request :: Set_Contains((locked_requests)[pid], req0) && req0->id == req->id);
    // assert {:layer 1} (participant_votes)[pid][req] == NULL();
    call voting1(req, pid);
}

action {:layer 1} ADD_TO_COMMITTED_REQUESTS( req: Request)
modifies committed_requests;
asserts !(exists req0:Request :: Set_Contains(committed_requests, req0) && req0->id == req->id);
asserts !(exists req1: Request :: req1->id != req->id && req1->duration == req->duration && Set_Contains(committed_requests, req1));
{
    committed_requests := Set_Add(committed_requests, req);
}
yield procedure {:layer 0} add_to_committed_requests( req: Request);
refines ADD_TO_COMMITTED_REQUESTS;

right action {:layer 1} RECEIVE_VOTE(pid: Pid, req: Request) returns (v: Vote)
{
   assume participant_votes[pid][req] != NULL();
   v := participant_votes[pid][req];
}
yield procedure {:layer 0} receive_vote(pid: Pid,  req: Request) returns (v: Vote);
refines RECEIVE_VOTE;

action {:layer 1} WAIT_FOR_PARTICIPANT_VOTE( req: Request)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==> participant_votes[pid][req] != NULL());
}
yield procedure {:layer 0} wait_for_participant_vote( req: Request); 
refines WAIT_FOR_PARTICIPANT_VOTE;

