------------------------ MODULE C_ProcedureBroadcast3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes, Nodes];

procedure f(i, msg) {
	Rec:
		broadcast(chan[i], msg);
		return;
}

{
	Lab:
		call f(1, "msg");
}

}
*)

================================================================================