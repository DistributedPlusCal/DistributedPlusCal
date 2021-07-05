------------------------ MODULE C_Receive3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)
CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

variables var;
channel chan[Nodes];

process (c \in Nodes)
{
	Lab:
		receive(chan[self], var);
}

}
*)

================================================================================