------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

fifo chan[Nodes, Nodes];

process w \in Nodes
begin
	Clear2:
      	    clear(chan[self]);
end process;
begin
        Clear:
                clear(chan);
end subprocess;
begin
        Clear3:
                clear(chan[self, self]);
end subprocess;


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-db305e264531d3c095e0e7b0bea20fd0
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..3]

Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes, _n1 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Clear2","Clear","Clear3">>]

Clear2(self) == /\ pc[self] [1] = "Clear2"
                /\ chan' = [_n0 \in Nodes, _n1 \in Nodes |->  IF _n0 = self THEN <<>>  ELSE chan[_n0, _n1]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Clear(self) == /\ pc[self] [2] = "Clear"
               /\ chan' = [_n0 \in Nodes, _n1 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

Clear3(self) == /\ pc[self] [3] = "Clear3"
                /\ chan' = [chan EXCEPT ![self, self] = <<>>]
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]

w(self) ==  \/ Clear2(self) \/ Clear(self) \/ Clear3(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2be95a70f5312858bed621926ac34fe9

==========================================================
