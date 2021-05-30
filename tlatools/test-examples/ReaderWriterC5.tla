------------------------ MODULE ReaderWriterC5 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N >= 2
Nodes == 1..N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

channel queue[Nodes];

process ( w \in Nodes )
variable cur = "none";
{
	Write:
  	while ( TRUE ) 
  	{
        send(queue[self], "msg");
  	};
  	Read:
  	while ( TRUE ) {
    	receive(queue[self], cur);
  	}
}

process ( r = 100 )
{
	Clear:
  		clear(queue);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-647da9cd11969b42018cf72b26dd540e
VARIABLES queue, pc, cur

vars == << queue, pc, cur >>

ProcSet == (Nodes) \cup {100}

SubProcSet == [_sub \in ProcSet |-> IF _sub \in Nodes THEN 1
                                   ELSE (**100**) 1]

Init == (* Global variables *)
        /\ queue = [n0 \in Nodes |-> {}]
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Write">>
                                        [] self = 100 -> <<"Clear">>]

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

Clear == /\ pc[100] [1] = "Clear"
         /\ queue' = [n0 \in Nodes |-> {}]
         /\ pc' = [pc EXCEPT ![100][1] = "Done"]
         /\ cur' = cur

r ==  \/ Clear

Next == r
           \/ (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3391e3c87e0e5f801b7d4a0f6c504aad

==========================================================
