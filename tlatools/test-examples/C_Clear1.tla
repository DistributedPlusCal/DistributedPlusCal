------------------------ MODULE C_Clear1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANT Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

channel chan;

process (c \in Nodes)
{
	Lab:
		clear(chan);
}

}
*)

================================================================================