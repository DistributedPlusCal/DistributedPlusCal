------------------------ MODULE DistTwoProcessesC -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MaxQueueSize

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable queue = <<>>;
fifo f_queue;

define {
  BoundedQueue == Len(queue) <= MaxQueueSize 
}

process ( w = "writer" )
{
	Write:
  	while ( TRUE ) 
  	{
    	queue := Append(queue, "msg");
      send(f_queue, "msg");
  	}
}

process ( r = "reader" )
variables current_message = "none";
{
	Read:
  	while ( TRUE ) {
    	receive(f_queue, current_message);
  	}
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bf65d048dfd77ec7aaa0236e8ca0818c
VARIABLES queue, f_queue, pc

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, f_queue, pc, current_message >>

ProcSet == {"writer"} \cup {"reader"}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 = "\"", "writer", "\"" THEN 1..1
                                 ELSE (**"\"", "reader", "\""**) 1..1]

Init == (* Global variables *)
        /\ queue = <<>>
        /\ f_queue = <<>>
        (* Process r *)
        /\ current_message = "none"
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> <<"Write">>
                                        [] self = "reader" -> <<"Read">>]

Write == /\ pc["writer"][1]  = "Write"
         /\ queue' = Append(queue, "msg")
         /\ f_queue' =  Append(f_queue, "msg")
         /\ pc' = [pc EXCEPT !["writer"][1] = "Write"]
         /\ UNCHANGED current_message

w == Write

Read == /\ pc["reader"][1]  = "Read"
        /\ Len(f_queue) > 0 
        /\ current_message' = Head(f_queue)
        /\ f_queue' =  Tail(f_queue)
        /\ pc' = [pc EXCEPT !["reader"][1] = "Read"]
        /\ queue' = queue

r == Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == w \/ r
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-cf229f194e7a4253749ddb40ea8c7488

==========================================================
