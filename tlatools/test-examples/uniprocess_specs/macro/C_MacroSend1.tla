------------------------ MODULE C_MacroSend1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {
 
channel chan;

macro send_to(msg) {
	send(chan, msg);
}

{
	Lab:
		send_to("abc");
}

}
*)

================================================================================