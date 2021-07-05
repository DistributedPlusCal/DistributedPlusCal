------------------------ MODULE C_MacroBroadcast1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan;

macro f() {
	broadcast(chan, "abc");
}

process (c \in Nodes)
{
	Lab:
		f();
}

}
*)

================================================================================