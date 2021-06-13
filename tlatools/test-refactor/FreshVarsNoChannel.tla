------------------------ MODULE FreshVarsNoChannel -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variables _n = 1, n1 = 2;

process (x = N+1)
variables t = <<1,2,3	>>;
{
    One:
		   t[1] := 1;
} 

process (id \in Nodes)
variables s = [no \in Nodes |-> 1];
{
    Two:
		   s[self] := 2;
}

}
*)
=========================================================
