------------------------ MODULE Procedures2p2tFixP -------------------------
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
    Addf:
        lv := lv + x + lp + c;
        c := x + 1;
        lp := lp + 11;
        return;
end procedure

procedure foo(y)
variable lvf = 0;
begin
    Addfoo:
        lvf := lvf + y + lq + c;
        lq := lq + 22;
        return;
end procedure

process pid = N
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
    Sdrq:
        call foo(lq);
    Afterq:
	    resq := lq;
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
	"compare_to": "test-procedures_process/Procedures2p2tFixC.tla"
}
