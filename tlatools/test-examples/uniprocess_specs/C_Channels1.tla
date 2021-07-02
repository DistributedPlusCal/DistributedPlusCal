------------------------ MODULE C_Channels1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {
 
variables x = 0;
channel chan;
fifo f_chan;

{
	Lab:
		x := x + 1;
}

}
*)

================================================================================