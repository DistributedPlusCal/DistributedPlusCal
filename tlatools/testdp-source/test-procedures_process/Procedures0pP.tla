------------------------ MODULE Procedures0pP -------------------------
EXTENDS TLC, Integers, Sequences
 
(*--algorithm Dummy 
variable c = 0, lp = 10, res = 1;

procedure f(x)
variable lv = 0;
begin
    Add:
        c := x + 1;
		lv := lv + 2;
		x := lv + 3;
	End:
        return;
end procedure

begin
    Before:
        lp := lp + 1;
    Sdr:
        call f(lp);
    After:
	    res := lp;
end algorithm
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
	},
    "compare_path": "compile",
	"compare_to": "test-procedures_process/Procedures0pC.tla"
}
