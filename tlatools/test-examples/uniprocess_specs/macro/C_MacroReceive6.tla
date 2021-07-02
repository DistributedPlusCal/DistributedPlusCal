------------------------ MODULE C_MacroReceive6 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable var, x = 0;
channel chan[Nodes,  Nodes];

macro send_to(msg, i, j, y) {
	receive(chan[i, j], msg);
	x := x + y;
}

{
	Lab:
		send_to(var, 1, 1, 10);
}

}
*)

================================================================================