------------------------ MODULE clockDeclaration4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes
Nodes == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

process ( w \in Nodes )
lamportClock clock1;
{
    Label1: 
        print(clock1);
} {
    Label2:
        print(clock1);
}

process (n \in {78, 79, 80})
lamportClock clock2;
{
    Lab:
        print(clock2);
}

}
*)


=========================================================