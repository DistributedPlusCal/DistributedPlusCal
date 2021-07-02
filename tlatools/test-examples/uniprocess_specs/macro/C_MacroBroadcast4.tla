------------------------ MODULE C_MacroBroadcast4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes, Nodes];

macro f(msg) {
	broadcast(chan, msg);
}

{
	Lab:
		f("abc");
}

}
*)

================================================================================