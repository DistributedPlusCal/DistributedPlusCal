------------------------ MODULE C_sendWithClock4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan;

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        sendWithClock(chan, "msg", clock);
}

}
*)


=========================================================