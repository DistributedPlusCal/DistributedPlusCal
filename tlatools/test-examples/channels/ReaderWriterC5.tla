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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-882360ca71ca8b2483f64c1d7686f943
VARIABLES queue, pc, cur

vars == << queue, pc, cur >>

ProcSet == (Nodes) \cup {100}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..1
                                   ELSE (**100**) 1..1]

Init == (* Global variables *)
        /\ queue = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Write">>
                                        [] self = 100 -> <<"Clear">>]

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

Clear == /\ pc[100][1]  = "Clear"
         /\ queue' = [_n0 \in Nodes |-> {}]
         /\ pc' = [pc EXCEPT ![100][1] = "Done"]
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a19b2209d5f346de36b28e78893c29dd

==========================================================
