------------------------ MODULE ReaderWriterC16 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variables c = 2;
fifo chan[Nodes, Nodes];

macro readFromChannel(x, i, y, j) {
    counter := counter + x;
    c := c - y;
    receive(chan[i, j], cur);
}

process ( w \in Nodes )
variable cur = "none", counter = 0;
{
	Read:
        readFromChannel(2, self, 5, self);
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-23b9e6d1108b5dfa97c6ec0f0a07fd69
VARIABLES c, chan, pc, cur, counter

vars == << c, chan, pc, cur, counter >>

ProcSet == (Nodes)

SubProcSet == [qtu21 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ c = 2
        /\ chan = [snt25 \in Nodes, yzc28 \in Nodes |-> <<>>]
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ counter = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Read(self) == /\ pc[self] [1] = "Read"
              /\ counter' = [counter EXCEPT ![self] = counter[self] + 2]
              /\ c' = c - 5
              /\ Len(chan[self, self]) > 0 
              /\ cur' = [cur EXCEPT ![self] = Head(chan[self, self])]
              /\ chan' = [chan EXCEPT ![self, self] =  Tail(chan[self, self]) ]
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Read(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7d21abbfb2237d7e39362e2c5bf973ea


========================================================
