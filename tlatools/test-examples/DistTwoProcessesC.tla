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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-cd2de7f523108fde800584835a55f14e
VARIABLES queue, f_queue

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, f_queue, current_message >>

ProcSet == {"writer"} \cup {"reader"}

SubProcSet == [n \in ProcSet |-> IF n = "\"", "writer", "\"" THEN 1
                           ELSE (**"\"", "reader", "\""**) 1]

w == /\ queue' = Append(queue, "msg")
     /\ f_queue' =  Append(@, "msg")
     /\ UNCHANGED current_message

r == /\ Len(f_queue) > 0 
     /\ current_message' = Head(f_queue)
     /\ f_queue' =  Tail(@) 
     /\ queue' = queue

Next == w \/ r

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f09828d408817764db37c0f4f038343

==========================================================
