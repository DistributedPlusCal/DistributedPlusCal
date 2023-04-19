------------------------ MODULE OneProcessSetMultiThreadPalt -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes

(* PlusCal options (-distpcal) *)

(*--algorithm dummy 

variables i = 1;

process w \in Nodes 
variables l = 2;
begin
	Write:
  	while ( i < 4 ) do
          i := i+1;
					l := l+2;
  	end while
end thread
begin
	Read:
  	while ( l < 10 ) do
          i := i+1;
					l := l+2;    	    
  	end while
end thread

end algorithm
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "Nodes": "1..3"
    }
}
