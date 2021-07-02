------------------------ MODULE C_ProcedureReceive3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable msg;
channel chan[Nodes, Nodes];

procedure f(i, j) {
	Rec:
		receive(chan[i, j], msg);
		return;
}

{
	Lab:
		call f(2, 2);
}

}
*)

================================================================================