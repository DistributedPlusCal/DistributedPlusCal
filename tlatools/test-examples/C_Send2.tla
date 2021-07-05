------------------------ MODULE C_Send2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

fifo chan;

process (c \in Nodes)
{
	Lab:
		send(chan, "msg");
}

}
*)

================================================================================