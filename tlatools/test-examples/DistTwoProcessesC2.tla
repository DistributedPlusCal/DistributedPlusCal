------------------------ MODULE DistTwoProcessesC2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MaxQueueSize

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable queue = <<>>;
channel chan;

define {
  BoundedQueue == Len(queue) <= MaxQueueSize 
}

process ( w = "writer" )
{
	Write:
  	while ( TRUE ) 
  	{
    	queue := Append(queue, "msg");
      send(chan, "msg");
  	}
}

process ( r = "reader" )
variables current_message = "none";
{
	Read:
  	while ( TRUE ) {
    	receive(chan, current_message);
  	}
}

}
*)

==========================================================
