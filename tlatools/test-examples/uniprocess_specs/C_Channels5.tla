------------------------ MODULE C_Channels5 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANTS Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variables x = 0;
channel chan[Nodes, Nodes];
fifo f_chan[Nodes, Nodes];

{
	Lab:
		x := x + 1;
}

}
*)

================================================================================