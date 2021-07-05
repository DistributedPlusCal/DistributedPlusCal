------------------------ MODULE C_sendWithClock2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

fifo chan[Nodes];

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        sendWithClock(chan[self], "msg", clock);
}

}
*)


=========================================================