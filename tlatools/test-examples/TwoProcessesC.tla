------------------------ MODULE TwoProcessesC -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MaxQueueSize

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable queue = <<>>;

define {
  BoundedQueue == Len(queue) <= MaxQueueSize 
}

process ( w = "writer" )
{
	Write:
  	while ( TRUE ) 
  	{
    	queue := Append(queue, "msg");
  	}
}

process ( r = "reader" )
variables current_message = "none";
{
	Read:
  	while ( TRUE ) {
    	current_message := Head(queue);
    	queue := Tail(queue);
  	}
}

}
*)

==========================================================
