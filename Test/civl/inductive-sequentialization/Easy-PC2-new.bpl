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
var {:layer 0,1} participant_votes: [Pid][ReqId]Vote;
var {:layer 0,1} committed_requests: (Set Request);



function {:inline} NoOverlap(req_set: (Set Request), d: Duration) : bool
{
    !(exists req: Request :: Set_Contains(req_set, req) && req->duration == d)
}

// yield invariant {:layer 1} YieldBig();
// invariant (forall pid: Pid, req: Request :: Set_Contains(locked_requests[pid], req) <==> participant_votes[pid][req->id] == YES());
// invariant !(exists pid: Pid, req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(locked_requests[pid], req1) && Set_Contains(locked_requests[pid], req2));
// invariant !(exists req1: Request, req2: Request :: req1->id != req2->id && req1->duration == req2->duration && Set_Contains(committed_requests, req1) && Set_Contains(committed_requests, req2));
// invariant !(exists req: Request, pid: Pid :: Set_Contains(committed_requests, req) && !Set_Contains(locked_requests[pid], req));

// yield invariant {:layer 1} YieldVoting({:linear} piece: One ParticipantPiece);
// invariant !(exists req0:Request :: Set_Contains(locked_requests[piece->val->id], req0) && req0->id == piece->val->val);
// invariant participant_votes[piece->val->id][piece->val->val] == NULL();

function {:inline} JParticipantIds(j: int): Set Pid {
    Set((lambda {:pool "P1"} x: int :: j <= x && x <= NumParticipants))
}

function {:inline} JParticipantPieces(r: ReqId, j: int): Set ParticipantPiece {
    Set((lambda {:pool "P2"} x: ParticipantPiece :: x->val == r && x->ids == ParticipantIds() && Set_Contains(JParticipantIds(j), x->id)))
}

function {:inline} AllParticipantPieces(r: ReqId): Set ParticipantPiece {
    Set((lambda {:pool "P2"} x: ParticipantPiece :: x->val == r && x->ids == ParticipantIds() && Set_Contains(x->ids, x->id)))
}
function {:inline} ParticipantIds(): Set Pid {
    Set((lambda {:pool "P1"} x: int :: 1 <= x && x <= NumParticipants))
}

function {:inline} IsValidParticipantPiece(x: ParticipantPiece): bool {
    x->ids == ParticipantIds() && Set_Contains(x->ids, x->id)
}

yield invariant {:layer 1} YieldInit({:linear} pieces: Set ParticipantPiece, req: Request);
invariant pieces == AllParticipantPieces(req->id);
invariant (forall p: ParticipantPiece :: Set_Contains(pieces, p) ==> participant_votes[p->id][p->val] == NULL());

yield invariant {:layer 1} YieldTrue();
invariant true;


yield procedure {:layer 1} coordinator({:linear_in} pieces: Set ParticipantPiece, req: Request)
requires call YieldInit(pieces, req);
// requires call YieldBig();

{
   var i: int;
   var j: int;
   var d: Decision;
   var v: Vote;
   var {:linear} pieces': Set ParticipantPiece;
   var {:linear} piece: One ParticipantPiece;
   pieces' := pieces;
   assume false;
   d := COMMIT();
   j := 1;
   while (j <= NumParticipants)
   invariant {:layer 1} 1 <= j && j <= NumParticipants + 1;
//    invariant {:layer 1} pieces == JParticipantPieces(reqId'->val, j);
   {
    call piece := One_Get(pieces', (Fraction(req->id, j, ParticipantIds())));
    async call voting0(req, piece);
    j := j + 1;
   }

//    call YieldBig();
   call YieldTrue();
   
   i := 1;
   while (i <= NumParticipants)
   {
    call v := receive_vote(i, req->id);
    if (v == NO())
    {
    d := ABORT();
    }
    i := i + 1;
   }

   call YieldTrue();

//    call YieldBig();

//    if (d == COMMIT()) {
//         // assert {:layer 1} false;
//         // all participants said yes
//         // locked requests of all pid have req
//         // committed => locked
//         // locked has no overlaps
//         assume false;
//         // assert {:layer 1} !(exists req1: Request :: req1->id != req->id && req1->duration == req->duration && Set_Contains(committed_requests, req1));
//         call add_to_committed_requests(req);
//    }
}

async action {:layer 1} voting(req: Request, {:linear_in} piece: One ParticipantPiece) //(reqid, pid) (4, 3) (5, 3)
modifies locked_requests, participant_votes;
asserts IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
// asserts !(exists req0:Request :: Set_Contains(locked_requests[pid], req0) && req0->id == req->id);
// asserts participant_votes[pid][req] == NULL();
{
    // assert !(exists req0:Request :: Set_Contains(locked_requests[pid->val->id], req0) && req0->id == req->id);
    // assert participant_votes[piece->val->id][piece->val->val] == NULL();
    // if (*) {
    //     participant_votes[pid->val->id][req] := NO();
    //     return;
    // }
    // else {
        
        if (NoOverlap(locked_requests[piece->val->id], req->duration)) {
            locked_requests[piece->val->id] := Set_Add(locked_requests[piece->val->id], req);
            participant_votes[piece->val->id][req->id] := YES();
        }
        else {
            participant_votes[piece->val->id][req->id] := NO();
        }
    // }
}
yield procedure {:layer 0} voting1(req: Request, {:linear_in} piece: One ParticipantPiece);
refines voting;

yield procedure {:layer 1} voting0(req: Request, {:linear_in}  piece: One ParticipantPiece)
requires {:layer 1} IsValidParticipantPiece(piece->val) && piece->val->val == req->id;
// requires call YieldBig();
// requires call YieldVoting(piece);
{
    // assert {:layer 1} !(exists req0:Request :: Set_Contains((locked_requests)[pid], req0) && req0->id == req->id);
    // assert {:layer 1} (participant_votes)[pid][req] == NULL();
    call voting1(req, piece);
}



action {:layer 1} ADD_TO_COMMITTED_REQUESTS(req: Request)
modifies committed_requests;
asserts !(exists req0:Request :: Set_Contains(committed_requests, req0) && req0->id == req->id);
asserts !(exists req1: Request :: req1->id != req->id && req1->duration == req->duration && Set_Contains(committed_requests, req1));
{
    committed_requests := Set_Add(committed_requests, req);
}
yield procedure {:layer 0} add_to_committed_requests(req: Request);
refines ADD_TO_COMMITTED_REQUESTS;



right action {:layer 1} RECEIVE_VOTE(pid: Pid, reqId: ReqId) returns (v: Vote)
{
   assume participant_votes[pid][reqId] != NULL();
   v := participant_votes[pid][reqId];
}
yield procedure {:layer 0} receive_vote(pid: Pid,  reqId: ReqId) returns (v: Vote);
refines RECEIVE_VOTE;



action {:layer 1} WAIT_FOR_PARTICIPANT_VOTE(reqId: ReqId)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= NumParticipants) ==> participant_votes[pid][reqId] != NULL());
}
yield procedure {:layer 0} wait_for_participant_vote(reqId: ReqId); 
refines WAIT_FOR_PARTICIPANT_VOTE;

