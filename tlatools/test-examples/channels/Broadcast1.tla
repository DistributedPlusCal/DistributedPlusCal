------------------------ MODULE Broadcast1 -------------------------
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
	broad2:
                 broadcast(fchan[self], "msg");
end process;
begin
        broad:
                broadcast(fchan, "msg");
end subprocess;
begin
        broad3:
                broadcast(fchan[self, self], "msg");
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bfb24cd68685e714ecce661c282e049b
VARIABLES fchan, pc

vars == << fchan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ fchan = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"broad2","broad","broad3">>]

broad2(self) == /\ pc[self][1]  = "broad2"
                /\ fchan' = [_n0 \in Nodes, _n1 \in Nodes |-> IF _n0 = self THEN  Append(fchan[_n0, _n1], "msg") ELSE fchan[_n0, _n1]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

broad(self) == /\ pc[self][2]  = "broad"
               /\ fchan' = [_n0 \in Nodes, _n1 \in Nodes |->  Append(fchan[_n0, _n1] , "msg")]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

broad3(self) == /\ pc[self][3]  = "broad3"
                /\ fchan' = [fchan EXCEPT ![self, self] =  Append(@, "msg")]
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]

w(self) == broad2(self) \/ broad(self) \/ broad3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-53f9945c5a9a7f4265210133c7b4eaca


==========================================================
