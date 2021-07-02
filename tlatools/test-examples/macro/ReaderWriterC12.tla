------------------------ MODULE ReaderWriterC12 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan[Nodes];

macro clear_channel() {
	clear(chan);
}

process ( w \in Nodes )
{
	Write:
        clear_channel();
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9727aadbd612229e5944c1b2785f7c49
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [_n0 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c4d2655031c66433a8ee6f84114c9de7

===========================================================================
