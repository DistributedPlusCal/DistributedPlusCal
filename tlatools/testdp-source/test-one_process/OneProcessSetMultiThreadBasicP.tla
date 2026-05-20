------------------------ MODULE OneProcessSetMultiThreadBasicP -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

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
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 3
    },
    "compare_to": ""
}
