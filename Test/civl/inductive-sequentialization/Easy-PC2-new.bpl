// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


// Assume Pid, ReqId are linear_in. Assume duration is an integer.

// C1: committed[req1] && committed[req2] ==> req1->duration != req2->duration
// C2: committed[req] ==> forall pid. participant_votes[pid][req] == YES() && Set_Contains(locked_requests[pid], req)
// C3: !(exists pid, req1, req2. req1->duration == req2->duration && participant_votes[pid][req1] == YES() && participant_votes[pid][req1] == YES())
// // C4: if-condition-before-updating-locked_requests-and-participant_votes ==> 
// C4: locked_requests does not contain requests with overlapping intervals

// where if-condition-before-updating-locked_requests-and-participant_votes:
// if (locked_requests[pid] does not contain any request that overlaps with req->duration) {
//             locked_requests[pid] := Set_Add(locked_requests[pid], req);
//             participant_votes[pid][req] := YES();
//         }

// Claim 1: C2 && C4 ==> C3 
// Claim 2: C2 && C3 ==> C1
// Do the claims make sense?

// C3 & C2 ==> C1
// 

type Pid = int;
type  Cid = int;
type Duration = int;

// type Time = int;

datatype Vote { YES(), NO(), NULL() }

datatype Decision { COMMIT(), ABORT(), NONE() }

type ReqId;

datatype Request { Request(id: ReqId, duration: Duration)}

const n:int;
axiom n > 0;

var {:layer 0,2} locked_requests: [Pid](Set Request);
var {:layer 0,2} participant_votes: [Pid][Request]Vote;
// var committed_durations: Set Duration;
var {:layer 0,2} committed_requests: (Set Request);

function {:inline} Init(participant_votes: [Pid][Request]Vote) : bool
{
  participant_votes == (lambda p:Pid :: (lambda r:Request  :: NULL())) 
}

function {:inline} NoOverlap(req_set: (Set Request), d: Duration) : bool
{
    !(exists req: Request :: Set_Contains(req_set, req) && req->duration == d)
}

// yield invariant {:layer 1} YieldInit();
// invariant Init(participant_votes); 

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

// atomic action {:layer 2} not_skip (req: Request) 
// {
//     assume (forall p:Pid :: 1 <= p && p <= n  ==> participant_votes[p][req] == YES() || participant_votes[p][req] == NO());
//     assume (forall p:Pid :: participant_votes[p][req] == YES() <==> Set_Contains(locked_requests[p], req));
//     assume (forall p:Pid :: participant_votes[p][req] == YES()) ==> Set_Contains(committed_requests, req);
// }

//keep 1, have a loop inside coordinator

yield procedure {:layer 1} coordinator( cid: Cid,  req: Request)
// refines not_skip;
// requires call YieldInit();
requires call YieldBig();
{
   var i: int;
   var d: Decision;
   var v: Vote;
   d := COMMIT();
   async call main_f(req);

   call YieldBig();
   
   i := 1;
   while (i <= n)
   {
    call v := receive_vote(i, req);
    if (v == NO())
    {
    d := ABORT();
    }
    i := i + 1;
   }

   if (d == COMMIT()) {
        // assert {:layer 1} false;
        // all participants said yes
        // locked requests of all pid have req
        // committed => locked
        // locked has no overlaps
        assert {:layer 1} !(exists req1: Request :: req1->id != req->id && req1->duration == req->duration && Set_Contains(committed_requests, req1));
        call add_to_committed_requests(req);
   }
}

// async action {:layer 2} MAIN_F'(req: Request){
//     assume (forall p:Pid :: 1 <= p && p <= n  ==> participant_votes[p][req] == YES() || participant_votes[p][req] == NO());
//     assume (forall p:Pid :: participant_votes[p][req] == YES() <==> Set_Contains(locked_requests[p], req));
// }


async action {:layer 1,2} MAIN_F( req: Request)
// refines {:IS_right} MAIN_F' using Inv;
creates voting;
{
    call create_asyncs((lambda pa: voting :: pa->req == req && pa->pid >= 1 && pa->pid <= n));
}
yield procedure {:layer 0} main_f(req: Request);
refines MAIN_F;

action {:layer 1} ADD_TO_COMMITTED_REQUESTS( req: Request)
modifies committed_requests;
{
    committed_requests := Set_Add(committed_requests, req);
}
yield procedure {:layer 0} add_to_committed_requests( req: Request);
refines ADD_TO_COMMITTED_REQUESTS;

right action {:layer 1} RECEIVE_VOTE( pid: Pid, req: Request) returns (v: Vote)
{
   assume participant_votes[pid][req] != NULL();
   v := participant_votes[pid][req];
}
yield procedure {:layer 0} receive_vote( pid: Pid,  req: Request) returns (v: Vote);
refines RECEIVE_VOTE;

// action {:layer 1,2} WAIT_FOR_PARTICIPANT_DECISION(req: Request)
// {
//       assume (forall pid: Pid :: (1 <= pid && pid <= n) ==> participant_decisions[pid][req] != NONE());
// }
// yield procedure {:layer 0} wait_for_participant_decision(req: Request); 
// refines WAIT_FOR_PARTICIPANT_DECISION;

action {:layer 1} WAIT_FOR_PARTICIPANT_VOTE( req: Request)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= n) ==> participant_votes[pid][req] != NULL());
}
yield procedure {:layer 0} wait_for_participant_vote( req: Request); 
refines WAIT_FOR_PARTICIPANT_VOTE;

async action {:layer 1,2} voting( req: Request,   pid: Pid)
modifies locked_requests, participant_votes;
{
    assert !(exists req0:Request :: Set_Contains(locked_requests[pid], req0) && req0->id == req->id);
    assert participant_votes[pid][req] == NULL();
    if (*) {
        participant_votes[pid][req] := NO();
        return;
    }
    else {
        
        if (NoOverlap(locked_requests[pid], req->duration)) {
            locked_requests[pid] := Set_Add(locked_requests[pid], req);
            participant_votes[pid][req] := YES();
        }
        else {
            participant_votes[pid][req] := NO();
        }
    }
}

// async action {:layer 1,2} MAIN_S(d: Decision, req: Request)
// creates deciding;
// {
//     call create_asyncs((lambda pa: deciding :: pa->decision == d && pa->req == req && pa->pid >= 1 && pa->pid <= n ));
// }
// yield procedure {:layer 0} main_s(d: Decision, req: Request);
// refines MAIN_S;

// async action {:layer 1,2} deciding(decision: Decision, req: Request, pid: Pid)
// modifies locked_requests, participant_decisions;
// {
//         if (decision == COMMIT()) {
//             participant_decisions[pid][req] := COMMIT();
//         }
//         else {
//              participant_decisions[pid][req] := ABORT();
//              //locked_requests
//             // locked_durations[pid] := Set_Remove(locked_durations[pid], req->duration);
//         }
// }

