------------------------ MODULE C_Receive4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

variables var;
fifo chan[Nodes];

process (c \in Nodes)
{
	Lab:
		receive(chan[self], var);
}

}
*)

================================================================================