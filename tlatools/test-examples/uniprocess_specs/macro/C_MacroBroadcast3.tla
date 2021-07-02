------------------------ MODULE C_MacroBroadcast3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

macro f(chan, msg) {
	broadcast(chan, msg);
}

{
	Lab:
		f("abc");
}

}
*)

================================================================================