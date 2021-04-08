------------------------		 MODULE ReaderWriterC1array -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Writer, Reader

(* PlusCal options (-distpcal) *)
 
(***
--algorithm message_queue {

fifo queue[Nat];

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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6a894adf20bc74ec7c327d48adc22487
VARIABLES queue, current_message

vars == << queue, current_message >>

ProcSet == {Writer} \cup {Reader}

SubProcSet == [n \in ProcSet |-> IF n = Writer THEN 1
                           ELSE (**Reader**) 1]

Init == (* Global variables *)
        /\ queue = [n0 \in Nat |-> <<>>]
        (* Node r *)
        /\ current_message = "none"

w == /\ queue' = [queue EXCEPT ![1] =  Append(queue[1], "msg")]
     /\ UNCHANGED current_message

r == /\ Len(queue[1]) > 0 
     /\ current_message' = Head(queue[1])
     /\ queue' = [queue EXCEPT ![1] =  Tail(queue[1]) ]

Next == w \/ r

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3703729257c228b92ab20e79a143571a
=============================================================================
