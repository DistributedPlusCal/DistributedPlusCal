------------------------ MODULE C_Clear4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

fifo chan[Nodes];

process (c \in Nodes)
{
	Lab1:
		clear(chan);
	Lab2:
		clear(chan[self]);
}

}
*)

================================================================================