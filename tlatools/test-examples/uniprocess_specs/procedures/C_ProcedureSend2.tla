------------------------ MODULE C_ProcedureSend2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {

variable msg = "abc";
channel chan;

procedure f(msg2) {
	Add:
		send(chan, msg2);
		return;
}

{
	Lab:
		call f(msg);
}

}
*)

================================================================================