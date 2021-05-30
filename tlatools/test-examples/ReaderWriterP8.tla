------------------------ MODULE ReaderWriterP8 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue

channel chan[Nodes];

macro sendToChannel(i) begin
	send(chan[self], "msg");
end macro;

process w \in Nodes
variable cur = "none";
begin
	Write:
  		sendToChannel(self);
end process;
begin
	Read:
    	receive(chan[self], cur);
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-040874dec619e41c1e9c0f3129a1289a
VARIABLES chan, pc, cur

vars == << chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = [n0 \in Nodes |-> {}]
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self] [2] = "Read"
              /\ \E c139 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {c139}]
                   /\ cur' = [cur EXCEPT ![self] = c139]
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) ==  \/ Write(self) \/ Read(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-65f79e9b7f7d8e9e395b14cb2b68d411


==============================================================
