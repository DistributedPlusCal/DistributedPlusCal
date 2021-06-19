------------------------ MODULE Broadcast3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan[Nodes, Nodes];

process w \in Nodes
begin
	broad2:
      	         broadcast(chan[self], "msg");
end process;
begin
        broad:
                broadcast(chan, "msg");
end subprocess;
begin
        broad3:
                broadcast(chan[self, self], "msg");
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ff89816836374b48637dec1f7d1381d4
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes, _n441 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"broad2","broad","broad3">>]

broad2(self) == /\ pc[self][1]  = "broad2"
                /\ chan' = [_n0 \in Nodes, _n1 \in Nodes |-> IF _n0 = self THEN chan[_n0, _n1] \cup {"msg"} ELSE chan[_n0, _n1]]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

broad(self) == /\ pc[self][2]  = "broad"
               /\ chan' = [_n0 \in Nodes, _n1 \in Nodes |-> chan[_n0, _n1] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

broad3(self) == /\ pc[self][3]  = "broad3"
                /\ chan' = [chan EXCEPT ![self, self] = chan[self, self] \cup {"msg"}]
                /\ pc' = [pc EXCEPT ![self][3] = "Done"]

w(self) == broad2(self) \/ broad(self) \/ broad3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4faebf29c53fe9c31d3d02e77b4f986c


==========================================================
