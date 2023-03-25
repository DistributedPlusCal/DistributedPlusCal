------------------------ MODULE Procedures2p2tC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

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
        lv := lv + x;
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
    Sdrq:
        call f(lq);
    Afterq:
	    resq := lq;
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
