------------------------ MODULE C_ProcedureSend4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

variable x = 1;
channel chan[Nodes];

procedure f(i, msg, y) {
	Add:
		send(chan[i], msg);
		x := x + y;
		return;
}

{
	Lab:
		call f(1, "abc", 2);
}

}
*)

================================================================================