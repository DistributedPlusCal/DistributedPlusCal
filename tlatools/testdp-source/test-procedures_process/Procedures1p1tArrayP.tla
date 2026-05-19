------------------------ MODULE Procedures1p1tArrayP -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(* PlusCal options (-label ) *)

(*--algorithm dummy 

variables ar = [ ind \in Nodes |-> ind ],  
          i = 2;


procedure change(arr, k)
begin
    P1:
        arr[k] := 0;
    P2:
	    return;
end procedure

process w = 1 
variables l = 2;
begin
    I:
	    i := 1;
    C:
        call change(ar,i);
    A:
	    await ar[1] = 0;
        i := i + 1;
end thread
end algorithm
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_path": "compile",
	"compare_to": "test-procedures_process/Procedures1p1tArrayC.tla"
}
