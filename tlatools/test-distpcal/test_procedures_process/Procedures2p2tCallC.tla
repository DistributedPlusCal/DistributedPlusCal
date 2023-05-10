------------------------ MODULE Procedures2p2tCallC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label -distpcal) *)

\* CONSTANT N 
N == 2
\* CONSTANT Nodes
Nodes == 1 .. N
 
(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 2;
{
    Addf:
        c := c + x + 3;
        return;
}

procedure foo(y)
variable lvf = 0;
{
    Foo:
        lvf := 1;
        c := c + y + 1;
    Callf:
        call f(lvf);
        return;
}

process (pid \in Nodes)
variable lp = 10, res = 1;
{
    Sdr:
        call foo(lp);
} 
{
    SdrS:
        call foo(lp);
} 

process (qid = N+1)
variable lq = 11, resq = 4;
{
    Sdrq:
        call foo(lq);
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
