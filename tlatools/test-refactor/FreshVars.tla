------------------------ MODULE FreshVars -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variables _n = 1, n1 = 2;
fifo chan[Nodes];

process (x = 1)
{
    Sdr:
        send(chan[self], "msg");
} 

}
*)
=========================================================
