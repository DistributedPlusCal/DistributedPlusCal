------------------------ MODULE C_broadcastWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        broadcastWithClock(chan, "msg", clock);
}

}
*)


=========================================================