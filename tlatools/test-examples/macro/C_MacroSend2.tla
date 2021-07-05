------------------------ MODULE C_MacroSend2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {
 
variable msg = "abc";
channel chan;

macro send_to() {
	send(chan, msg);
}

process (c \in Nodes)
{
	Lab:
		send_to();
}

}
*)

================================================================================