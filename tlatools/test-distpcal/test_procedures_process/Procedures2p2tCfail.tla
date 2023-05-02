------------------------ MODULE Procedures2p2tCfail -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label -distpcal) *)

\* CONSTANT N 
N == 2
\* CONSTANT Nodes
Nodes == 1 .. N
 
(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Add:
        lv := lv + x + lp + c;
        c := x + 1;
        return;
}

process (pid \in Nodes)
variable lp = 10, res = 1;
{
    Before:
	    lp := lp + 1;
    Sdr:
        call f(lp);
    After:
	    res := lp;
} 
{
    BeforeS:
	    lp := lp + 1;
    SdrS:
        call f(lp);
	AfterS:
	    res := lp;
} 

process (qid = N+1)
variable lq = 11, resq = 4;
{
    Beforeq:
	    lq := lq + 1;
    Sdrq: \* the procedure uses a variable local to process(es) pid and thus, can't be called from another process
        call f(lq);
    Afterq:
	    resq := lq;
} 
} 
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    }
}
