------------------------ MODULE C_MacroSendWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

macro f(i, msg, clock) {
    sendWithClock(chan[i], msg, clock);
}

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        f(self, "msg", clock);
}

}
*)


=========================================================