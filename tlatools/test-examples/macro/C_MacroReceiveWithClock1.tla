------------------------ MODULE C_MacroReceiveWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variable var;
channel chan[Nodes];

macro f(i, var, clock) {
    receiveWithClock(chan[i], var, clock);
}

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        f(self, var, clock);
}

}
*)


=========================================================