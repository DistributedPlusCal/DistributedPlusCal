------------------------ MODULE C_MacroSendWithClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

procedure f(i, msg, clock) {
    Lab:
        sendWithClock(chan[i], msg, clock);
        return;
}

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        call f(self, "msg", clock);
}

}
*)


=========================================================