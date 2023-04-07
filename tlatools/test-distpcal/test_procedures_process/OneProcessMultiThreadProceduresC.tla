------------------------ MODULE OneProcessMultiThreadProceduresC -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy {

variables ar = [ ind \in Nodes |-> ind ],  
          i = 2;


procedure change(arr, k)
{
    P1:
    arr[k] := 0;
    P2:
	return;
}

process ( w = 1 )
variables l = 2;
{
    I:
	i := 1;
    C:
    call change(ar,i);
} {
    A:
	await ar[1] = 0;
    i := i + 1;
}
}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    }
}
