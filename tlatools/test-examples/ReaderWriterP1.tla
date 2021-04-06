------------------------ MODULE ReaderWriterP1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm f_queue_algo

variable cur = "none";
fifo f_queue;

process w = "writer"
begin
	Write:
  	while ( TRUE ) do
    	    send(f_queue, "msg");
  	end while;
end process;

process r = "reader"
begin
	Read:
  	while ( TRUE ) do
    	     receive(f_queue, cur);
  	end while;
end process;

end algorithm;
*)

==========================================================
