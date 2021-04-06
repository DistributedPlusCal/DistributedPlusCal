------------------------ MODULE ReaderWriterP2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variable cur = "none";
channel chan[Nodes];

process w \in Nodes
begin
	Write:
  	while ( TRUE ) do
      	    send(chan[self], "msg");
  	end while;
end process;

process r \in Nodes
begin
	Read:
  	while ( TRUE ) do
    	    receive(chan[self], cur);
  	end while;
end process;

end algorithm;
*)

==========================================================
