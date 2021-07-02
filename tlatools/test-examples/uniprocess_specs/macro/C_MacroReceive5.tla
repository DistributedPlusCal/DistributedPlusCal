------------------------ MODULE C_MacroReceive5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable var;
channel chan[Nodes,  Nodes];

macro send_to(msg, i, j) {
	receive(chan[i, j], msg);
}

{
	Lab:
		send_to(var, 1, 1);
}

}
*)

================================================================================