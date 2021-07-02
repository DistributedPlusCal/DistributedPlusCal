------------------------ MODULE C_MacroMulticast3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable x = 0;
channel chan[Nodes, Nodes];

macro f(exp) {
	broadcast(chan, exp);
}

{
	Lab:
		f([a \in Nodes, b \in Nodes |-> "msg"]);
}

}
*)

================================================================================