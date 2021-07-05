------------------------ MODULE clockDeclaration2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        print(clock);
}

process (n = 78)
{
    Lab:
        skip;
}

}
*)


=========================================================