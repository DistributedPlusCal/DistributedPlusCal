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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7b751bd73d18bb16f9196da0a4f21785
VARIABLES c, chan, pc, cur, counter

vars == << c, chan, pc, cur, counter >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ c = 2
        /\ chan = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ counter = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Read(self) == /\ pc[self][1]  = "Read"
              /\ counter' = [counter EXCEPT ![self] = counter[self] + 2]
              /\ c' = c - 5
              /\ Len(chan[self, self]) > 0 
              /\ cur' = [cur EXCEPT ![self] = Head(chan[self, self])]
              /\ chan' = [chan EXCEPT ![self, self] =  Tail(@) ]
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-bbdd3ca02b9ae48710aee99963200183


========================================================
