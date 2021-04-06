------------------------ MODULE ReaderWriterC2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
channel chan;

process ( w = "writer" )
{
	Write:
  	while ( TRUE ) 
  	{
            send(chan, "msg");
  	}
}

process ( r = "reader" )
{
	Read:
  	while ( TRUE ) {
    	     receive(chan, cur);
  	}
}

}
*)

==========================================================
