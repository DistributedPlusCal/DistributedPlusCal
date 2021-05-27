------------------------ MODULE Clear2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel fchan[Nodes, Nodes];

process w \in Nodes
begin
	clear2:
                 clear(fchan[self]);
end process;
begin
        clear:
                clear(fchan);
end subprocess;
begin
        clear3:
                clear(fchan[self, self]);
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e6cd1bb84a0673cd7a318b9acad79227
VARIABLES fchan, pc

vars == << fchan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..3]

Init == (* Global variables *)
        /\ fchan = [_n0 \in Nodes, _n1 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"clear2","clear","clear3">>]

clear2(self) == /\ pc[self] [1] = "clear2"
                /\ fchan' = [_n0, _n1 \in Nodes |-> IF _n0 = self THEN {} ELSE fchan[_n0, _n1]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

clear(self) == /\ pc[self] [2] = "clear"
               /\ fchan' = [_n0, _n1 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

clear3(self) == /\ pc[self] [3] = "clear3"
                /\ fchan' = [fchan EXCEPT ![self, self] = {}]
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]

w(self) ==  \/ clear2(self) \/ clear(self) \/ clear3(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d7675a6df36ed5a6e325a88235daa282


==========================================================
