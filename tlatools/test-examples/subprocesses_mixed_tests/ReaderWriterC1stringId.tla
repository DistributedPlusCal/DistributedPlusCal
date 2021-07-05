------------------------ MODULE ReaderWriterC1stringId -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)
 
(*
--algorithm message_queue {

fifo queue;

process ( w = "writer" )
{
	Write:
  	while ( TRUE ) 
  	{
      	    send(queue, "msg");
  	}
}

process ( r = "reader" )
variable current_message = "none";
{
	Read:
  	while ( TRUE ) {
    	    receive(queue, current_message);
  	}
}

}
*)
=============================================================================
