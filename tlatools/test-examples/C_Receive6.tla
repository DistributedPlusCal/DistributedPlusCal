------------------------ MODULE C_Receive6 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)
CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

variables var;
fifo chan[Nodes, Nodes];

process (c \in Nodes)
{
	Lab:
		receive(chan[self, self], var);
}

}
*)

================================================================================