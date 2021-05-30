------------------------ MODULE ReaderWriterP6 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan[Nodes];

process w \in Nodes
variable cur = "none", count = 0;
begin
	Write:
      	broadcast(chan, "msg");
end process;
begin
	Read:
    	receive(chan[self], cur);
end subprocess;
begin
	Clear:
	await ( count = 5 );
	clear(chan);
	count := 0;
end subprocess;

end algorithm;
*)

==========================================================