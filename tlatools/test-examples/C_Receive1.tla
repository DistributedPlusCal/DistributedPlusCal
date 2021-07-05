------------------------ MODULE C_Receive1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANT Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

variables var;
channel chan;

process (c \in Nodes)
{
	Lab:
		receive(chan, var);
}

}
*)

================================================================================