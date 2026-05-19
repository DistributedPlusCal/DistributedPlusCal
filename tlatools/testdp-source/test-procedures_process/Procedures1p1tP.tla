------------------------ MODULE Procedures1p1tP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label  ) *)

(*--algorithm Dummy 
variable c = 0;

procedure f(x)
variable lv = 0;
begin
    Add:
        c := x + 1;
				lv := lv + 2;
				x := lv + 3;
        return;
end procedure

process id = 2
variable lp = 10, res = 1;
begin
    Before:
        lp := lp + 1;
    Sdr:
        call f(lp);
    After:
        res := lp;
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
	"compare_to": "test-procedures_process/Procedures1p1tC.tla"
}
