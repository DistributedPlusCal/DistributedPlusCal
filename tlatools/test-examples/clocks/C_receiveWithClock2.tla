------------------------ MODULE C_receiveWithClock2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variable var;
fifo chan[Nodes];

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        receiveWithClock(chan[self], var, clock);
}

}
*)


=========================================================