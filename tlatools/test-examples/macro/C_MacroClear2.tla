------------------------ MODULE C_MacroClear2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan;

macro f(chan) {
	clear(chan);
}

process (c \in Nodes)
{
	Lab:
		f(chan);
}

}
*)

================================================================================