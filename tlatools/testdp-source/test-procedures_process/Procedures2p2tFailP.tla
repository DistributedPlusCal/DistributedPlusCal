------------------------ MODULE Procedures2p2tFailP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label ) *)

\* CONSTANT N 
N == 2
\* CONSTANT Nodes
Nodes == 1 .. N
 
(*--algorithm Dummy 
variable c = 0;

procedure f(x)
variable lv = 0;
begin
    Add:
        lv := lv + x + lp + c;
        c := x + 1;
        return;
end procedure

process pid \in Nodes
variable lp = 10, res = 1;
begin
    Before:
	    lp := lp + 1;
    Sdr:
        call f(lp);
    After:
	    res := lp;
end thread

process qid = N+1
variable lq = 11, resq = 4;
begin
    Beforeq:
	    lq := lq + 1;
    Sdrq: \* the procedure uses a variable local to process(es) pid and thus, can't be called from another process
        call f(lq);
    Afterq:
	    resq := lq;
end thread
end algorithm
*)
=============================================================================
{
    "expect-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_path": "compile",
	"compare_to": "test-procedures_process/Procedures2p2tFailC.tla"
}
