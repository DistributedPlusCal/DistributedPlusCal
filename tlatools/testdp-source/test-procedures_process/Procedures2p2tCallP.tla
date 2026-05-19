------------------------ MODULE Procedures2p2tCallP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label ) *)

\* CONSTANT N 
N == 2
\* CONSTANT Nodes
Nodes == 1 .. N
 
(*--algorithm Dummy 
variable c = 0;

procedure f(x)
variable lv = 2;
begin
    Addf:
        c := c + x + 3;
        return;
end procedure

procedure foo(y)
variable lvf = 0;
begin
    Foo:
        lvf := 1;
        c := c + y + 1;
    Callf:
        call f(lvf);
        return;
end procedure

process pid \in Nodes
variable lp = 10, res = 1;
begin
    Sdr:
        call foo(lp);
end thread
begin
    SdrS:
        call foo(lp);
end thread

process qid = N+1
variable lq = 11, resq = 4;
begin
    Sdrq:
        call foo(lq);
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
	"compare_to": "test-procedures_process/Procedures2p2tCallC.tla"
}
