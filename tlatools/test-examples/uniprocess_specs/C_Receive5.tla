------------------------ MODULE C_Receive5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)
CONSTANTS Nodes
Nodes == 1..3

(*
--algorithm seq_algo {

variables var;
channel chan[Nodes, Nodes];

{
	Lab:
		receive(chan[2, 1], var);
}

}
*)

================================================================================