------------------------ MODULE C_Send4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes;
Nodes == 1..3

(*
--algorithm seq_algo {

fifo chan[Nodes];

{
	Lab:
		send(chan[2], "msg");
}

}
*)

================================================================================