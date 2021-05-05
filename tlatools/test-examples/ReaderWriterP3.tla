------------------------ MODULE ReaderWriterP3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan[Nodes];

process w \in Nodes
begin
	Write:
  	while ( TRUE ) do
      	    send(chan[self], "msg");
  	end while;
end process;


end algorithm;
*)

==========================================================
