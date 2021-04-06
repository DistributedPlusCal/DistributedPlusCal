------------------------ MODULE ReaderWriterC1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
fifo f_queue;

process ( w = "writer" )
{
	Write:
  	while ( TRUE ) 
  	{
      	    send(f_queue, "msg");
  	}
}

process ( r = "reader" )
{
	Read:
  	while ( TRUE ) {
    	    receive(f_queue, current_message);
  	}
}

}
*)

==========================================================
