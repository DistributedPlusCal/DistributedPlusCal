------------------------ MODULE C_ProcedureReceive1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable msg;
channel chan;

procedure f() {
	Rec:
		receive(chan, msg);
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