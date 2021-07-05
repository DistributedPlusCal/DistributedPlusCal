------------------------ MODULE C_Broadcast2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANT Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

fifo chan;

process (c \in Nodes)
{
	Lab:
		broadcast(chan, "msg");
}

}
*)

================================================================================