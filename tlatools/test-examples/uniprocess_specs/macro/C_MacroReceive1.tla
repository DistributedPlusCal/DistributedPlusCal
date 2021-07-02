------------------------ MODULE C_MacroReceive1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable x = 0, var;
channel chan;

macro send_to(msg, y) {
	receive(chan, msg);
	x := x + y
}

{
	Lab:
		send_to(var, 5);
}

}
*)

================================================================================