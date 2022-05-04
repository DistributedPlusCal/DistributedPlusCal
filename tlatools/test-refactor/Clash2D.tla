------------------------ MODULE Clash2D -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. 3

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
variable cur = "none";

fifo chan[Nodes,Nodes];

process ( w \in Nodes )
{
	Write1:
    send(chan[self,self], "msg");
}
{
	Write2:
    send(chan[self,self], "msg");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-73e35a3b5be5c58feaa29f4d0e30518d
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n20 \in Nodes, _n31 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write1","Write2">>]

Write1(self) == /\ pc[self][1]  = "Write1"
                /\ chan' = [chan EXCEPT ![self,self] =  Append(@, "msg")]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ cur' = cur

Write2(self) == /\ pc[self][2]  = "Write2"
                /\ chan' = [chan EXCEPT ![self,self] =  Append(@, "msg")]
                /\ pc' = [pc EXCEPT ![self][2] = "Done"]
                /\ cur' = cur

w(self) == Write1(self) \/ Write2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b4b22e1567f74ffb7b77a1b39d6723a8
==========================================================

