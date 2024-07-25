// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;
type Cid = int;
type Duration = int;

// type Time = int;

datatype Vote { YES(), NO(), NULL() }

datatype Decision { COMMIT(), ABORT(), NONE() }

type ReqId;

datatype Request { Request(id: ReqId, duration: Duration)}

const n:int;
axiom n > 0;

var locked_requests: [Pid](Set Request);
var participant_votes: [Pid][Request]Vote;
var participant_decisions: [Pid][Request]Decision;
// var committed_requests: [Cid](Set Request);
// var locked_durations: [Pid](Set Duration);
var committed_durations: Set Duration;


function {:inline} Init(participant_votes: [Pid][Request]Vote, participant_decisions: [Pid][Request]Decision) : bool
{
  participant_votes == (lambda p:Pid :: (lambda r:Request  :: NULL())) &&
  participant_decisions == (lambda p:Pid :: (lambda r:Request  :: NONE()))
}

yield invariant {:layer 1} YieldInit();
invariant Init(participant_votes, participant_decisions); 

yield procedure {:layer 1} coordinator(cid: Cid, req: Request)
// refines skip;
requires call YieldInit();
{
   var i: int;
   var d: Decision;
   var v: Vote;
   d := COMMIT();
   async call main_f(req);
   call wait_for_participant_vote(req);
   i := 1;
   while (i <= n)
   {
    call v := receive_vote(i, req);
    if (v == NO())
    {
    d := ABORT();
    break;
    }
    i := i + 1;
   }
   async call main_s(d, req);
   call wait_for_participant_decision(req);
   if (d == COMMIT()) {
        assert {:layer 1} !(Set_Contains(committed_durations, req->duration));
        call add_to_committed_durations(req);
   }
}

async action {:layer 1,2} MAIN_F(req: Request)
creates voting;
{
    call create_asyncs((lambda pa: voting :: pa->req == req && pa->pid >= 1 && pa->pid <= n ));
}
yield procedure {:layer 0} main_f(req: Request);
refines MAIN_F;

async action {:layer 1,2} ADD_TO_COMMITTED_DURATIONS(req: Request)
modifies committed_durations;
{
    committed_durations := Set_Add(committed_durations, req->duration);
}
yield procedure {:layer 0} add_to_committed_durations(req: Request);
refines ADD_TO_COMMITTED_DURATIONS;

action {:layer 1,2} RECEIVE_VOTE(pid: Pid, req: Request) returns (v: Vote)
{
   v := participant_votes[pid][req];
}
yield procedure {:layer 0} receive_vote(pid: Pid, req: Request) returns (v: Vote);
refines RECEIVE_VOTE;

action {:layer 1,2} WAIT_FOR_PARTICIPANT_DECISION(req: Request)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= n) ==> participant_decisions[pid][req] != NONE());
}
yield procedure {:layer 0} wait_for_participant_decision(req: Request); 
refines WAIT_FOR_PARTICIPANT_DECISION;

action {:layer 1,2} WAIT_FOR_PARTICIPANT_VOTE(req: Request)
{
      assume (forall pid: Pid :: (1 <= pid && pid <= n) ==> participant_votes[pid][req] != NULL());
}
yield procedure {:layer 0} wait_for_participant_vote(req: Request); 
refines WAIT_FOR_PARTICIPANT_VOTE;

async action {:layer 1,2} voting(req: Request, pid: Pid)
modifies locked_durations, participant_votes;
{
    if (*) {
        participant_votes[pid][req] := NO();
        return;
    }
    else {
        if (!Set_Contains(locked_durations[pid], req->duration) && !Set_Contains(committed_durations, req->duration)) {
            locked_durations[pid] := Set_Add(locked_durations[pid], req->duration);
            participant_votes[pid][req] := YES();
        }
        else {
            participant_votes[pid][req] := NO();
        }
    }
}

async action {:layer 1,2} MAIN_S(d: Decision, req: Request)
creates deciding;
{
    call create_asyncs((lambda pa: deciding :: pa->decision == d && pa->req == req && pa->pid >= 1 && pa->pid <= n ));
}
yield procedure {:layer 0} main_s(d: Decision, req: Request);
refines MAIN_S;

async action {:layer 1,2} deciding(decision: Decision, req: Request, pid: Pid)
modifies locked_durations, participant_decisions;
{
        if (decision == COMMIT()) {
            participant_decisions[pid][req] := COMMIT();
        }
        else {
             participant_decisions[pid][req] := ABORT();
            locked_durations[pid] := Set_Remove(locked_durations[pid], req->duration);
        }
}

