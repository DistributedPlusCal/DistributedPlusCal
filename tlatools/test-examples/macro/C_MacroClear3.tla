------------------------ MODULE C_MacroClear3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

macro f(i) {
	clear(chan[i]);
}

process (c \in Nodes)
{
	Lab:
		f(self);
}

}
*)

================================================================================