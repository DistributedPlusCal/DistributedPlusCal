------------------------ MODULE C_MacroClear4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes, Nodes];

macro f(i) {
	clear(chan[i]);
}

{
	Lab:
		f(1);
}

}
*)

================================================================================