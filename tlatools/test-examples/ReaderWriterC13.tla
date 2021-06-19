------------------------ MODULE ReaderWriterC13 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan[Nodes, Nodes];

macro broadcast_channel(expr) {
	broadcast(chan, expr);
}

macro multicast_channel(expr2) {
	multicast(chan, expr2);
}

process ( w \in Nodes )
{
	Write1:
        broadcast_channel("msg");
    Write2:
    	multicast(chan, [self, a \in Nodes |-> "abc"])
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1718926736aa1a7914b7276507bd6ab1
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write1">>]

Write1(self) == /\ pc[self][1]  = "Write1"
                /\ chan' = [_n0 \in Nodes, _n1 \in Nodes |->  Append(chan[_n0, _n1] , "msg")]
                /\ pc' = [pc EXCEPT ![self][1] = "Write2"]

Write2(self) == /\ pc[self][1]  = "Write2"
                /\ chan' = [<<slf, a>> \in DOMAIN chan |->  IF slf = self 
                            /\ a \in Nodes THEN 
                            Append(chan[slf, a], "abc") ELSE chan[slf, a]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write1(self) \/ Write2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-cc2cf0721a7d8450dcac37a78ae28a8c

===========================================================================
