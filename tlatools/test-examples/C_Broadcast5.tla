------------------------ MODULE C_Broadcast5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

channel chan[Nodes, Nodes];

process (c \in Nodes)
{
	Lab1:
		broadcast(chan, "msg");
	Lab2:
		broadcast(chan[self], "abc");
}

}
*)

================================================================================