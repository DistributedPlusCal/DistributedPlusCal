------------------------ MODULE ReaderWriterP5 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel queue[Nodes];

process w \in Nodes
variable cur = "none";
begin
	Write:
  	while ( TRUE ) do
      	    send(queue[self], "msg");
  	end while;
  	Read:
  	while ( TRUE ) do
    	    receive(queue[self], cur);
  	end while;
end process;

process r = "r"
begin
  Clear:
      clear(queue);
end process;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e5068514998b485c2036ee705b991ab7
VARIABLES queue, pc, cur

vars == << queue, pc, cur >>

ProcSet == (Nodes) \cup {"r"}

SubProcSet == [n \in ProcSet |-> IF n \in Nodes THEN 1
                             ELSE (**"\"", "r", "\""**) 1]

Init == (* Global variables *)
        /\ queue = [n0 \in Nodes |-> {}]
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Write">>
                                        [] self = "r" -> <<"Clear">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ queue' = [queue EXCEPT ![self] = queue[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self] [1] = "Read"
              /\ \E q139 \in queue[self]:
                   /\ cur' = [cur EXCEPT ![self] = q139]
                   /\ queue' = [queue EXCEPT ![self] = queue[self] \ {q139}]
              /\ pc' = [pc EXCEPT ![self][1] = "Read"]

w(self) ==  \/ Write(self) \/ Read(self)

Clear == /\ pc["r"] [1] = "Clear"
         /\ queue' = [n0 \in Nodes |-> {}]
         /\ pc' = [pc EXCEPT !["r"][1] = "Done"]
         /\ cur' = cur

r ==  \/ Clear

Next == r
           \/ (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-40cd5b536980344639449a0e56b5dad2

========================================================
