------------------------ MODULE Procedures2p2tFixC -------------------------
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
    Addf:
        lv := lv + x + lp + c;
        c := x + 1;
        lp := lp + 11;
        return;
}

procedure foo(y)
variable lvf = 0;
{
    Addfoo:
        lvf := lvf + y + lq + c;
        lq := lq + 22;
        return;
}

process (pid = N)
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
        call foo(lq);
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
