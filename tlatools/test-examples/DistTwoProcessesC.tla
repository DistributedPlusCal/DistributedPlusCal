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

==========================================================
