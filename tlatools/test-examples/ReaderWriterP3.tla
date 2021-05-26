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
      	    broadcast(chan[self], "msg");
end process;
begin
        Clear:
                broadcast(chan, "msg");
end subprocess;


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2d7bb34bcbf153c6bf661ddebccf3314
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Clear2","Clear">>]

Clear2(self) == /\ pc[self] [1] = "Clear2"
                /\ chan' = [chan EXCEPT ![self] =  Append(@, "msg")]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Clear(self) == /\ pc[self] [2] = "Clear"
               /\ chan' = [_n0 \in Nodes |->  Append(chan[_n0] , "msg")]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) ==  \/ Clear2(self) \/ Clear(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0274bd47d545455d41619df4ac38f3c1

==========================================================
