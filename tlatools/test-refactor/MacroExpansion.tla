------------------------ MODULE MacroExpansion.tla -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variables ar = [i \in 1..2 |-> 3];
fifo chan[Nodes];

macro send_to(i, msg) {
  ar[i] := ar[i]+1;
  \* send(chan[i], msg);
}


process ( w \in Nodes )
{
    Mc:
        send_to(self, "abc");
}


}
*)



================================================
