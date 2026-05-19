------------------------ MODULE Procedures0pC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label  ) *)

(*--algorithm Dummy {
variable c = 0, lp = 10, res = 1;

procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
		lv := lv + 2;
		x := lv + 3;
	End:
        return;
}

{
    Before:
        lp := lp + 1;
    Sdr:
        call f(lp);
    After:
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
