------------------------ MODULE SequentialClearP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

channel chan;

begin
	Clear:
		clear(chan);
	Add:
		send(chan, 2);
	ClearAgain:
		clear(chan);


end algorithm;
*)

===========================================
