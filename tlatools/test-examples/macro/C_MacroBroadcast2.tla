------------------------ MODULE C_MacroBroadcast2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

macro f(msg) {
	broadcast(chan, msg);
}

process (c \in Nodes)
{
	Lab:
		f("abc");
}

}
*)

================================================================================