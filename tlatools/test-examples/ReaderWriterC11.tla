------------------------ MODULE ReaderWriterC11 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*
--algorithm message_queue {

variables c = 0, d = 5;
fifo chan[Nodes];

macro sendToChannel(msg, i, x, y) {
	send(chan[i], msg);
	d := d + x;
	c := c + y;
}

process ( w \in Nodes )
{
	Write:
        sendToChannel("abc", self, 4, 10);
} 
  
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-99c555d934ff6f5b96e8fbcbe4d65f4a
VARIABLES c, d, chan, pc

vars == << c, d, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ c = 0
        /\ d = 5
        /\ chan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] =  Append(@, "abc")]
               /\ d' = d + 4
               /\ c' = c + 10
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ab7e8262449f0fbd2d6fb9f7ece61772


========================================================
