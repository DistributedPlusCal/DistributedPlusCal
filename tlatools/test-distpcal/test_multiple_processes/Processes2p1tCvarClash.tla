------------------------ MODULE Processes2p1tCvarClash -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm PotentialVarClash {

\* try to find names in conflict with generated fresh variables
variables _n1 = 1, _n2 = 2, _n42 = 42, n1 = 2;

process (x = N+1)
variables t = <<1,2,3>>;
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
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
		    "N": 2
    }
}
