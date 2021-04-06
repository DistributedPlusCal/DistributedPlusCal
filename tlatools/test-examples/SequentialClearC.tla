------------------------ MODULE SequentialClearC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

channel chan;

{
	Clear:
		clear(chan);
	Add:
		send(chan, 2);
	ClearAgain:
		clear(chan);
}

}
*)

===========================================
