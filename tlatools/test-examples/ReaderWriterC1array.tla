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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0832c3ff6c14cd5a4c4b922c97f55700
VARIABLES queue, pc, current_message

vars == << queue, pc, current_message >>

ProcSet == {Writer} \cup {Reader}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 = Writer THEN 1..1
                                 ELSE (**Reader**) 1..1]

Init == (* Global variables *)
        /\ queue = [_n430 \in Nat |-> <<>>]
        (* Process r *)
        /\ current_message = "none"
        /\ pc = [self \in ProcSet |-> CASE self = Writer -> <<"Write">>
                                        [] self = Reader -> <<"Read">>]

Write == /\ pc[Writer][1]  = "Write"
         /\ queue' = [queue EXCEPT ![1] =  Append(@, "msg")]
         /\ pc' = [pc EXCEPT ![Writer][1] = "Write"]
         /\ UNCHANGED current_message

w == Write

Read == /\ pc[Reader][1]  = "Read"
        /\ Len(queue[1]) > 0 
        /\ current_message' = Head(queue[1])
        /\ queue' = [queue EXCEPT ![1] =  Tail(@) ]
        /\ pc' = [pc EXCEPT ![Reader][1] = "Read"]

r == Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == w \/ r
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-eee4ec19f0fe469bf3665657a64d9021
=============================================================================
