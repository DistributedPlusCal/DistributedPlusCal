------------------------ MODULE C_Send1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

channel chan;

{
	Lab:
		send(chan, "msg");
}

}
*)

================================================================================