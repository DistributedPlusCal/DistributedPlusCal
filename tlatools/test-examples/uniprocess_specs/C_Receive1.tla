------------------------ MODULE C_Receive1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

variables var;
channel chan;

{
	Lab:
		receive(chan, var);
}

}
*)

================================================================================