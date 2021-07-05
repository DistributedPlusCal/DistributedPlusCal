------------------------ MODULE C_ProcedureClear2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

procedure f(i) {
	Rec:
		clear(chan[i]);
		return;
}

process (c \in Nodes)
{
	Lab:
		call f(self);
}

}
*)

================================================================================