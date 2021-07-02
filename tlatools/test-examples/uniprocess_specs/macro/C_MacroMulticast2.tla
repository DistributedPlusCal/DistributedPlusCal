------------------------ MODULE C_MacroMulticast2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable x = 0;
channel chan[Nodes];

macro f(exp, y) {
	broadcast(chan, exp);
	x := x + y; \* this is added to test that parameters are correctly handled
}

{
	Lab:
		f([a \in Nodes |-> "msg"]);
}

}
*)

================================================================================