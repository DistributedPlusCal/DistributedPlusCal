------------------------ MODULE C_ProcedureSend3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

channel chan[Nodes];

procedure f(i, msg) {
	Add:
		send(chan[i], msg);
		return;
}

{
	Lab:
		call f(1, "abc");
}

}
*)

================================================================================