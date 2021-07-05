------------------------ MODULE C_ProcedureClear1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan;

procedure f() {
	Rec:
		clear(chan);
		return;
}

process (c \in Nodes)
{
	Lab:
		call f();
}

}
*)

================================================================================