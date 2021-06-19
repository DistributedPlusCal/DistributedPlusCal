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

process r = 99
begin
  Clear:
      clear(queue);
end process;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b208293c66b6a73ade13e3e89b3c6fc5
VARIABLES queue, pc, cur

vars == << queue, pc, cur >>

ProcSet == (Nodes) \cup {99}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..1
                                   ELSE (**99**) 1..1]

Init == (* Global variables *)
        /\ queue = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Write">>
                                        [] self = 99 -> <<"Clear">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ queue' = [queue EXCEPT ![self] = queue[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self][1]  = "Read"
              /\ \E _q139 \in queue[self]:
                   /\ cur' = [cur EXCEPT ![self] = _q139]
                   /\ queue' = [queue EXCEPT ![self] = queue[self] \ {_q139}]
              /\ pc' = [pc EXCEPT ![self][1] = "Read"]

w(self) == Write(self) \/ Read(self)

Clear == /\ pc[99][1]  = "Clear"
         /\ queue' = [_n0 \in Nodes |-> {}]
         /\ pc' = [pc EXCEPT ![99][1] = "Done"]
         /\ cur' = cur

r == Clear

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == r
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-68327a049abb036b4af49f122cca0f23

========================================================
