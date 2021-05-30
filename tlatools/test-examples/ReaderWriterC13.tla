------------------------ MODULE ReaderWriterC13 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan[Nodes];

macro broadcast_channel(expr) {
	broadcast(chan, expr);
}

macro multicast_channel(expr2) {
	multicast(chan, expr2);
}

process ( w \in Nodes )
{
	Write1:
        broadcast_channel([a \in chan |-> "msg"]);
    Write2:
    	multicast_channel([a \in chan |-> "abc"])
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1edc908f1311e302833cb77b77c49d9c
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [ybv14 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = [cnc20 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write1">>]

Write1(self) == /\ pc[self] [1] = "Write1"
                /\ chan' = [a \in DOMAIN chan |->  IF a \in chan THEN 
                            Append(chan[a], "msg") ELSE chan[a]]
                /\ pc' = [pc EXCEPT ![self][1] = "Write2"]

Write2(self) == /\ pc[self] [1] = "Write2"
                /\ chan' =  Append(chan, [a \in chan |-> "abc"])
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Write1(self) \/ Write2(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-324475b882f642668ea36a291603665c

===========================================================================
