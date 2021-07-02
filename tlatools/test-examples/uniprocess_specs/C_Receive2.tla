------------------------ MODULE C_Receive2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

variables var;
fifo chan;

{
	Lab:
		receive(chan, var);
}

}
*)

================================================================================