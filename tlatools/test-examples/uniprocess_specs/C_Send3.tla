------------------------ MODULE C_Send3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes;
Nodes == 1..3

(*
--algorithm seq_algo {

channel chan[Nodes];

{
	Lab:
		send(chan[1], "msg");
}

}
*)

================================================================================