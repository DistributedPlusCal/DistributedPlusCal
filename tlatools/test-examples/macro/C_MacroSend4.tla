------------------------ MODULE C_MacroSend4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

macro send_to(msg, i) {
	send(chan[i], msg);
}

process (c \in Nodes)
{
	Lab:
		send_to("abc", self);
}

}
*)

================================================================================