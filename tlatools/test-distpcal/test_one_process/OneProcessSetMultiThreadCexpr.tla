------------------------ MODULE OneProcessSetMultiThreadCexpr -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*--algorithm dummy {

variables i = 1;

process ( w \in Nodes \cup {N+1} \cup N+2..N+3)
variables l = 2;
{
	Write:
  	    l := l+2;
} {
	Read:
  	    l := l+4;
}
}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 3
    }
}
