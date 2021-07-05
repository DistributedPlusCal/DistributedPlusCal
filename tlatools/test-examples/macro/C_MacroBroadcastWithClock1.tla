------------------------ MODULE C_MacroBroadcastWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

macro f(msg, clock) {
    broadcastWithClock(chan, msg, clock);
}

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        f("msg", clock);
}

}
*)


=========================================================