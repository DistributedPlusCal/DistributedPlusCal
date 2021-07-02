------------------------ MODULE C_Send2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

fifo chan;

{
	Lab:
		send(chan, "msg");
}

}
*)

================================================================================