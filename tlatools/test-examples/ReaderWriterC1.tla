------------------------ MODULE ReaderWriterC1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Writer, Reader

(* PlusCal options (-distpcal) *)
 
(***
--algorithm message_queue {

fifo queue;

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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-92e9a53b18804e31e1bdd47c240d2abf
VARIABLES queue, current_message

vars == << queue, current_message >>

ProcSet == {Writer} \cup {Reader}

SubProcSet == [n \in ProcSet |-> IF n = Writer THEN 1
                           ELSE (**Reader**) 1]

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process r *)
        /\ current_message = "none"

w == /\ queue' =  Append(@, "msg")
     /\ UNCHANGED current_message

r == /\ Len(queue) > 0 
     /\ current_message' = Head(queue)
     /\ queue' =  Tail(@) 

Next == w \/ r

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-15b0fdd62ee4af23558ace42ec6a77eb
=============================================================================
