------------------------ MODULE C_MacroReceiveWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variable var;
channel chan[Nodes];

procedure f(i, var, clock) {
    Lab:
        receiveWithClock(chan[i], var, clock);
        return;
}

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        call f(self, var, clock);
}

}
*)


=========================================================