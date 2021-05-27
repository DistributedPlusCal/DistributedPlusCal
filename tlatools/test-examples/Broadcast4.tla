------------------------ MODULE Broadcast4 -------------------------
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
	broad2:
                 broadcast(chan[self], "msg");
end process;
begin
        broad:
                broadcast(chan, "msg");
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b41fe435053b1ad52d8afda4874a8f01
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"broad2","broad">>]

broad2(self) == /\ pc[self] [1] = "broad2"
                /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]

broad(self) == /\ pc[self] [2] = "broad"
               /\ chan' = [_n0 \in Nodes |-> chan[_n0] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) ==  \/ broad2(self) \/ broad(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-86450814c92d8c405c6c597d522886cc


==========================================================
