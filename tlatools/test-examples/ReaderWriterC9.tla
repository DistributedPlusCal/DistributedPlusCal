------------------------ MODULE ReaderWriterC9 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {


channel chan[Nodes];

macro send_to(i, msg) {
    send(chan[i], msg);
}

macro receive_from_channel(x, msg, i) {
    cur := cur + x;
    send_to(i, msg);
}

macro cl() {
    clear(chan);
}

process ( w \in Nodes )
variable cur = 0;
{
    Read:
      receive_from_channel(3, "msg", self);
} {
    Clear:
    cl();
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e723dbe0f9a5d5f86b9c064e075a2208
VARIABLES chan, pc, cur

vars == << chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Read","Clear">>]

Read(self) == /\ pc[self][1]  = "Read"
              /\ cur' = [cur EXCEPT ![self] = cur[self] + 3]
              /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Clear(self) == /\ pc[self][2]  = "Clear"
               /\ chan' = [_n0 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ cur' = cur

w(self) == Read(self) \/ Clear(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6858e6a5c3770b8ef934594d2dc84d5b



=========================================================
