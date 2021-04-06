------------------------ MODULE SequentialAlgoC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

channel chan;

process rm = 1 
begin
	Start:
	send(chan, 2);
end process;

end algorithm;
*)

==========================================================
