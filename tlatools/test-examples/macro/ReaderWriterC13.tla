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
	send(chan, expr);
}

macro f2(expr2) {
	multicast(chan, expr2);
}

process ( w \in Nodes )
{
    Write2:
        f2([self, a \in Nodes |-> "abc"]);
	Write1:
        broadcast_channel("msg");

} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-43fe2aa0e9c0270bc38b84057f03cdf6
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_mn430 \in Nodes, _mn441 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write2">>]

Write2(self) == /\ pc[self][1]  = "Write2"
                /\ chan' = [<<slf, a>> \in DOMAIN chan |->  IF slf = self 
                            /\ a \in Nodes THEN 
                            Append(chan[slf, a], "abc") ELSE chan[slf, a]]
                /\ pc' = [pc EXCEPT ![self][1] = "Write1"]

Write1(self) == /\ pc[self][1]  = "Write1"
                /\ chan' =  Append(@, "msg")
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write2(self) \/ Write1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4dae12d3c40bb0e6d6e1cb38a0407e76

===========================================================================
