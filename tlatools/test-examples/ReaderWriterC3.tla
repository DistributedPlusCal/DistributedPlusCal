------------------------ MODULE ReaderWriterC3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
channel chan[Nodes];

process ( w \in Nodes )
{
	Write:
  	while ( TRUE ) 
  	{
            send(chan[self], "msg");
  	}
}
process ( r \in Nodes )
{
	Read:
  	while ( TRUE ) {
    	     receive(chan[self], cur);
  	}
}
}
*)

==========================================================
