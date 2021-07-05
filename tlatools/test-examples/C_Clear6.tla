------------------------ MODULE C_Clear6 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

fifo chan[Nodes, Nodes];

process (c \in Nodes)
{
	Lab1:
		clear(chan);
	Lab2:
		clear(chan[self]);
	Lab3:
		clear(chan[self, self])
}

}
*)

================================================================================