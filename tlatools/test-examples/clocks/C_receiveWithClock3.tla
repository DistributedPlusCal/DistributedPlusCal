------------------------ MODULE C_receiveWithClock3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variable var;
channel chan;

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        receiveWithClock(chan, var, clock);
}

}
*)


=========================================================