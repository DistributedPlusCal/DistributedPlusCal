------------------------ MODULE C_MacroReceive2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable var;
channel chan;

macro send_to() {
	receive(chan, msg);
}

{
	Lab:
		send_to();
}

}
*)

================================================================================