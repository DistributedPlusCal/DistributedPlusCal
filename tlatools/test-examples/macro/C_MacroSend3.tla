------------------------ MODULE C_MacroSend3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

macro send_to(i, msg) {
	send(chan[i], msg);
}

process (c \in Nodes)
{
	Lab:
		send_to(self, "abc");
}

}
*)

================================================================================