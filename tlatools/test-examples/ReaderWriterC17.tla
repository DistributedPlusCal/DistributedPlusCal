------------------------ MODULE ReaderWriterC17 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan;

macro readFromChannel(x) {
    counter := counter + x;
    receive(chan, cur);
}

process ( w \in Nodes )
variable cur = "none", counter = 0;
{
	Read:
        readFromChannel(2);
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-218ba066184176ab9e4909915ae8ca2f
VARIABLES chan, pc, cur, counter

vars == << chan, pc, cur, counter >>

ProcSet == (Nodes)

SubProcSet == [dtj13 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = <<>>
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ counter = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Read(self) == /\ pc[self] [1] = "Read"
              /\ counter' = [counter EXCEPT ![self] = counter[self] + 2]
              /\ Len(chan) > 0 
              /\ cur' = [cur EXCEPT ![self] = Head(chan)]
              /\ chan' =  Tail(chan) 
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Read(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5ee1193350a57cd3e380af59f5abc024


========================================================
