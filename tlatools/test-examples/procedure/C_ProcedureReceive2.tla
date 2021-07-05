------------------------ MODULE C_ProcedureReceive2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variable msg;
channel chan[Nodes];

procedure f(i, msg2) {
	Rec:
		receive(chan[i], msg2);
		return;
}

process (c \in Nodes)
{
	Lab:
		call f(self, msg);
}

}
*)

================================================================================