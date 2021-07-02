------------------------ MODULE C_Send6 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes;
Nodes == 1..3

(*
--algorithm seq_algo {

fifo chan[Nodes, Nodes];

{
	Lab:
		send(chan[2, 1], "msg");
}

}
*)

================================================================================