------------------------ MODULE Procedures0pP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy 
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
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
		},
    "compare_path": "compare",
		"compare_to": "test_procedures_process/Procedures0pPCAL.tla"
}
