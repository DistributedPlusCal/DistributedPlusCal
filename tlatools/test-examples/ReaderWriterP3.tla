------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan[Nodes];

process w \in Nodes
begin
	Write:
  	while ( TRUE ) do
      	    send(chan[self], "msg");
  	end while;
end process;
begin
        Clear:
                clear(chan);
end subprocess;


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-dc93a63c91faacfd8d5ebb2e6e55068a
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"Write","Clear">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]

Clear(self) == /\ pc[self] [2] = "Clear"
               /\ chan' = [_n0 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) ==  \/ Write(self) \/ Clear(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-99aded01b947352f682c9ca6d6c0961f

==========================================================
