------------------------ MODULE OneProcessSetMultiThreadC -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*--algorithm dummy {

variables i = 1;

process ( w \in Nodes )
variables l = 2;
{
	Write:
  	while ( i < 4 ) 
  	{
          i := i+1;
					l := l+2;
  	}
} {
	Read:
  	while ( l < 10 ) {
          i := i+1;
					l := l+2;    	    
  	}
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
