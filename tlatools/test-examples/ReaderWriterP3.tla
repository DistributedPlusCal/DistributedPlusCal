------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

fifo chan[Nodes];

process w \in Nodes
begin
	Clear2:
      	    clear(chan[self]);
end process;
begin
        Clear:
                clear(chan);
end subprocess;


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-72da768f038cb6a8dbbfde560fbddaa9
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Clear2","Clear">>]

Clear2(self) == /\ pc[self] [1] = "Clear2"
                /\ chan' = [chan EXCEPT ![self] = <<>>]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Clear(self) == /\ pc[self] [2] = "Clear"
               /\ chan' = [_n0 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) ==  \/ Clear2(self) \/ Clear(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-16f2a3ab8d9f401fddb0dc141f4c80e0

==========================================================
