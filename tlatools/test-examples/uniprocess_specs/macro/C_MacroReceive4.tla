------------------------ MODULE C_MacroReceive4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable var, x = 0;
channel chan[Nodes];

macro send_to(i, msg, y) {
	receive(chan[i], msg);
	x := x + y;
}

{
	Lab:
		send_to(1, var, 10);
}

}
*)

================================================================================