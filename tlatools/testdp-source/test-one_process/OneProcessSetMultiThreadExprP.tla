------------------------ MODULE OneProcessSetMultiThreadExprP -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(*--algorithm dummy 

variables i = 1;

process w \in Nodes \cup {N+1} \cup N+2..N+3
variables l = 2;
begin
	Write:
  	    l := l+2;
end thread;
begin
	Read:
  	    l := l+4;
end thread;

end algorithm;
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 3
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessSetMultiThreadExprC.tla"
}
