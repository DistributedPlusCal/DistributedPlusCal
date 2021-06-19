------------------------ MODULE Clear1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

fifo fchan[Nodes, Nodes];

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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-360590e564a25d46392cb786d6d06a99
VARIABLES fchan, pc

vars == << fchan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ fchan = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"clear2","clear","clear3">>]

clear2(self) == /\ pc[self][1]  = "clear2"
                /\ fchan' = [_n0, _n1 \in Nodes |->  IF _n0 = self THEN <<>>  ELSE fchan[_n0, _n1]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

clear(self) == /\ pc[self][2]  = "clear"
               /\ fchan' = [_n0, _n1 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

clear3(self) == /\ pc[self][3]  = "clear3"
                /\ fchan' = [fchan EXCEPT ![self, self] = <<>>]
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]

w(self) == clear2(self) \/ clear(self) \/ clear3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b78e47abd4554323a9ec800ddb3735e6


==========================================================
