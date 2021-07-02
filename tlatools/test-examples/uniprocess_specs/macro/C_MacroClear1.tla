------------------------ MODULE C_MacroClear1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan;

macro f() {
	clear(chan);
}

{
	Lab:
		f();
}

}
*)

================================================================================