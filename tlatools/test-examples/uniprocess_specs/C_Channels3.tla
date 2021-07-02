------------------------ MODULE C_Channels3 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..5

(*
--algorithm seq_algo {
 
variables x = 0;
channel chan[Nodes];
fifo f_chan[Nodes];

{
	Lab:
		x := x + 1;
}

}
*)

================================================================================