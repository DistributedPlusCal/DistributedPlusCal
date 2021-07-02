------------------------ MODULE C_Clear5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

channel chan[Nodes, Nodes];

{
	Lab1:
		clear(chan);
	Lab2:
		clear(chan[2]);
	Lab3:
		clear(chan[2, 2])
}

}
*)

================================================================================