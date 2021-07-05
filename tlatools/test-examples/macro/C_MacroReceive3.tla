------------------------ MODULE C_MacroReceive3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable var;
channel chan[Nodes];

macro send_to(i, msg) {
	receive(chan[i], msg);
}

process (c \in Nodes)
{
	Lab:
		send_to(self, var);
}

}
*)

================================================================================