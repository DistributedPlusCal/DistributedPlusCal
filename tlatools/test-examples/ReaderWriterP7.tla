------------------------ MODULE ReaderWriterP7 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue

variable cur = "none";
channel chan[Nodes];

process w \in Nodes
begin
	Write:
      	send(chan[self], "msg");
end process;
begin
	Read:
    	receive(chan[self], cur);
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9997fbc70842959aff8a3f7f1ec40185
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [n0 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self] [2] = "Read"
              /\ \E c149 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {c149}]
                   /\ cur' = c149
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) ==  \/ Write(self) \/ Read(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-cb2823594e3da89bc533aa9c13c61fd9

================================================================
