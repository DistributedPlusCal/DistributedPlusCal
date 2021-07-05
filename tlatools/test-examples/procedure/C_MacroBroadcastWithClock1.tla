------------------------ MODULE C_MacroBroadcastWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

procedure f(msg, clock) {
    Lab:
        broadcastWithClock(chan, msg, clock);
        return;
}

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        call f("msg", clock);
}

}
*)


=========================================================