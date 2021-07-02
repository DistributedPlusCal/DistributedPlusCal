------------------------ MODULE C_Broadcast4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

fifo chan[Nodes]

{
	Lab1:
		broadcast(chan, "msg");
}

}
*)

================================================================================