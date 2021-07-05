------------------------ MODULE C_Send5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes;
Nodes == 1..3

(*
--algorithm seq_algo {

channel chan[Nodes, Nodes];

process (c \in Nodes)
{
	Lab:
		send(chan[self, self], "msg");
}

}
*)

================================================================================