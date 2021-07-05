------------------------ MODULE C_ProcedureBroadcast2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
channel chan[Nodes];

procedure f(msg) {
	Rec:
		broadcast(chan, msg);
		return;
}

process (c \in Nodes)
{
	Lab:
		call f("msg");
}

}
*)

================================================================================