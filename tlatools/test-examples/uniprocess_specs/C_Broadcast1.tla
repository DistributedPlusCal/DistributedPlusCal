------------------------ MODULE C_Broadcast1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

channel chan;

{
	Lab:
		broadcast(chan, "msg");
}

}
*)

================================================================================