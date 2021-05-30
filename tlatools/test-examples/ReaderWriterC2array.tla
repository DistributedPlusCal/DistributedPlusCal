------------------------		 MODULE ReaderWriterC1array -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Writer, Reader

(* PlusCal options (-distpcal) *)
 
(***
--algorithm message_queue {

channel queue[Nat];

process ( w = Writer )
{
	Write:
  	while ( TRUE ) 
  	{
      	    send(queue[1], "msg");
  	}
}

process ( r = Reader )
variable current_message = "none";
{
	Read:
  	while ( TRUE ) {
    	    receive(queue[1], current_message);
  	}
}

}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b61101a665c042d847fb08708b354b7f
VARIABLES queue, current_message

vars == << queue, current_message >>

ProcSet == {Writer} \cup {Reader}

SubProcSet == [n \in ProcSet |-> IF n = Writer THEN 1
                           ELSE (**Reader**) 1]

Init == (* Global variables *)
        /\ queue = [n0 \in Nat |-> {}]
        (* Node r *)
        /\ current_message = "none"

w == /\ queue' = [queue EXCEPT ![1] = queue[1] \cup {"msg"}]
     /\ UNCHANGED current_message

r == \E q119 \in queue[1]:
       /\ current_message' = q119
       /\ queue' = [queue EXCEPT ![1] = queue[1] \ {q119}]

Next == w \/ r

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-86909122465862a232f8fce1009e9229
=============================================================================
