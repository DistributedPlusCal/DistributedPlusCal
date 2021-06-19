------------------------ MODULE ReaderWriterC14 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variables c = 3;
fifo chan;

macro send_to(x, msg) {
    c := c + x;
    send(chan, msg);
}

process ( w \in Nodes )
{
	Write:
        send_to(2, "abc");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3499998673c37ed5b44edd98a8dfeea4
VARIABLES c, chan, pc

vars == << c, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ c = 3
        /\ chan = <<>>
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ c' = c + 2
               /\ chan' =  Append(chan, "abc")
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b9f8a54cc49bafd914ff2725c7879e98


========================================================
