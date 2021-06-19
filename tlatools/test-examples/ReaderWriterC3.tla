------------------------ MODULE ReaderWriterC3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan[Nodes];

process ( w \in Nodes )
{
	Write:
         send(chan[self], "msg");
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-08b1dfa2967d86e9c056012a53be8f06
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] =  Append(@, "msg")]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-02475acf08bafc537e45c2ebd5f9c0b1

==========================================================
