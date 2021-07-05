------------------------ MODULE C_Channels1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

CONSTANT Nodes
Nodes == 1..4

(*
--algorithm seq_algo {
 
variables x = 0;
channel chan;
fifo f_chan;

process (c \in Nodes)
{
	Lab:
		x := x + 1;
}

}
*)

================================================================================