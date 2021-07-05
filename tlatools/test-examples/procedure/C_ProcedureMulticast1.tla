------------------------ MODULE C_ProcedureMulticast1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

procedure f(expr) {
	Rec:
		clear(chan, expr);
		return;
}

process (c \in Nodes)
{
	Lab:
		call f([a \in Nodes |-> "abc"]);
}

}
*)

================================================================================