------------------------ MODULE C_MacroMulticast1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

macro f(exp) {
	broadcast(chan, exp);
}

{
	Lab:
		f([a \in Nodes |-> "msg"]);
}

}
*)

================================================================================