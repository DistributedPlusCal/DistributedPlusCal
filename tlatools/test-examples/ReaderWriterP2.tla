------------------------ MODULE ReaderWriterP2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variable cur = "none";
channel chan;

process w = "Writer"
begin
	Write:
  	while ( TRUE ) do
      	    send(chan, "msg");
  	end while;
end process;

process r = "Reader"
begin
	Read:
  	while ( TRUE ) do
    	    receive(chan, cur);
  	end while;
end process;

end algorithm;
*)

==========================================================
