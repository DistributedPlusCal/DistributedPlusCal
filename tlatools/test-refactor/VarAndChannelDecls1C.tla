------------------------ MODULE VarAndChannelDecls1C -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. 3
NN == 1 .. 2
NS == 1 .. 4

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
variable cur = "none";
channels chan[NS];

process ( w \in Nodes )
variable c = 4;
fifo fifs[NN];
{
	Lab:
	  c := c+1;
	Snd:
    send(fifs[1], "msg");
	\* Snd2:
    \* send(chan[self], "msg");
	Rcv:
	  receive(fifs[1], cur);
	\* Rcv2:
	  \* receive(chan[self], cur);
}

}
*)
==========================================================

