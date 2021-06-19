------------------------ MODULE ReaderWriterC1 -------------------------
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3f6727800ac3f17fc110ceb9462bb6e7
VARIABLES queue, pc, current_message

vars == << queue, pc, current_message >>

ProcSet == {Writer} \cup {Reader}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 = Writer THEN 1..1
                                 ELSE (**Reader**) 1..1]

Init == (* Global variables *)
        /\ queue = {}
        (* Process r *)
        /\ current_message = "none"
        /\ pc = [self \in ProcSet |-> CASE self = Writer -> <<"Write">>
                                        [] self = Reader -> <<"Read">>]

Write == /\ pc[Writer][1]  = "Write"
         /\ queue' = (queue \cup {"msg"})
         /\ pc' = [pc EXCEPT ![Writer][1] = "Write"]
         /\ UNCHANGED current_message

w == Write

Read == /\ pc[Reader][1]  = "Read"
        /\ \E _q119 \in queue:
             /\ current_message' = _q119
             /\ queue' = queue \ {_q119}
        /\ pc' = [pc EXCEPT ![Reader][1] = "Read"]

r == Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == w \/ r
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f7dddc8ff458cabafc47b5976a02c97c
=============================================================================
