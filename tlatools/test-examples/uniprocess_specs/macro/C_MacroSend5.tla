------------------------ MODULE C_MacroSend5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable x = 0;
channel chan[Nodes];

macro send_to(msg, i, y) {
	send(chan[i], msg);
	x := x + y
}

{
	Lab:
		send_to("abc", 1, 5);
}

}
*)

================================================================================