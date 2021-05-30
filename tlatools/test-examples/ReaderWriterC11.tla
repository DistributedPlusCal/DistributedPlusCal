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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6d0fd1748aca3806a01d1c10aa7b80cd
VARIABLES c, d, chan, pc

vars == << c, d, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [htl25 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ c = 0
        /\ d = 5
        /\ chan = [yyi26 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self] =  Append(chan[self], "abc")]
               /\ d' = d + 4
               /\ c' = c + 10
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Write(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-025fabca84be2f62a17907eaa5667df6


========================================================
