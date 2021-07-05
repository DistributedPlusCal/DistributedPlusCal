------------------------ MODULE C_MacroBroadcast5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes, Nodes];

macro f(i, msg) {
	broadcast(chan[i], msg);
}

process (c \in Nodes)
{
	Lab:
		f(self, "abc");
}

}
*)

================================================================================