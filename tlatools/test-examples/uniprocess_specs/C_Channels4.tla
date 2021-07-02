------------------------ MODULE C_Channels4 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {
 
variables x = 0;
channel chan[1..3, 1..3];
fifo f_chan[2..5, 2..5];

{
	Lab:
		x := x + 1;
}

}
*)

================================================================================