 ------------------------ MODULE ReaderWriterC2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Writer, Reader

(* PlusCal options (-distpcal) *)
 
(***
--algorithm message_queue {

channel queue;

process ( w = Writer )
{
	Write:
  	while ( TRUE ) 
  	{
      	    send(queue, "msg");
  	}
}

process ( r = Reader )
variable current_message = "none";
{
	Read:
  	while ( TRUE ) {
    	    receive(queue, current_message);
  	}
}

}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-294123121c6375e29fb3682c6b7a9e41
VARIABLES queue, current_message

vars == << queue, current_message >>

ProcSet == {Writer} \cup {Reader}

SubProcSet == [n \in ProcSet |-> IF n = Writer THEN 1
                           ELSE (**Reader**) 1]

Init == (* Global variables *)
        /\ queue = {}
        (* Node r *)
        /\ current_message = "none"

w == /\ queue' = (queue \cup {"msg"})
     /\ UNCHANGED current_message

r == \E q119 \in queue:
       /\ current_message' = q119
       /\ queue' = queue \ {q119}

Next == w \/ r

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7ce57835db968d1b827bd3177ba951dd
=============================================================================
