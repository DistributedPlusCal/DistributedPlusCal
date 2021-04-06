------------------------ MODULE ReaderWriterC4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
fifo f_chan[Nodes];

process ( w \in Nodes )
{
	Write:
  	while ( TRUE ) 
  	{
            send(f_chan[self], "msg");
  	}
}
process ( r \in Nodes )
{
	Read:
  	while ( TRUE ) {
    	     receive(f_chan[self], cur);
  	}
}
}
*)

==========================================================
