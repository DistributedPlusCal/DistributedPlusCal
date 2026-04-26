------------------------ MODULE OneProcessSetMultiThreadPexpr -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

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
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 3
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessSetMultiThreadCexpr.tla"
}
