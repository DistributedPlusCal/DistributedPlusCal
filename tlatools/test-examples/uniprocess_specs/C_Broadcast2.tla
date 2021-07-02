------------------------ MODULE C_Broadcast2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

fifo chan;

{
	Lab:
		broadcast(chan, "msg");
}

}
*)

================================================================================