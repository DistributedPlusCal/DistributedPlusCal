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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bead33fa6708b91612058bc6c48d755f
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [rly27 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = [voj17 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [sfa18 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Write(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-adfba5e0d5d5f5643057998e52418791

===========================================================================
