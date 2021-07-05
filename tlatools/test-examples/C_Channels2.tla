------------------------ MODULE C_Channels2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANT Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variables x = 0;
channel chan[1..3];
fifo f_chan[2..5];

process (c \in Nodes)
{
	Lab:
		x := x + 1;
}

}
*)

================================================================================