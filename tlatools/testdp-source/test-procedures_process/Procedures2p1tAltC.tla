------------------------ MODULE Procedures2p1tAltC -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N
 
(* PlusCal options (-label ) *)

(*--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
		lv := lv + 2;
		x := lv + 3;
        return;
}

process (id = N+1)
variable lp = 10, res = 1;
{
    Before:
	    lp := lp + 1;
    Sdr:
        call f(lp);
    After:
        res := lp;
} 

process (idm \in Nodes)
variable lp = 10, res = 1;
{
    BeforeS:
        lp := lp + 1;
    SdrS:
        call f(lp);
    AfterS:
        res := lp;
} 

} 
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_to": ""
}
