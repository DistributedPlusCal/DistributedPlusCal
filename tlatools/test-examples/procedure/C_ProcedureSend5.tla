------------------------ MODULE C_ProcedureSend5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

channel chan[Nodes];

procedure f(msg, i, j) {
	Add:
		send(chan[i, j], msg);
		return;
}

process (c \in Nodes)
{
	Lab:
		call f("abc", self, self);
}

}
*)

================================================================================