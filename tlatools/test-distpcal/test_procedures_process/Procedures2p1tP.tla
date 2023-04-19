------------------------ MODULE Procedures2p1tP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT Nodes     (* Set of process indexes *)
Nodes == 1 .. N
 
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

process id = N+1
variable lp = 10, res = 1;
begin
   Before:
	      lp := lp + 1;
   Sdr:
        call f(lp);
	 After:
	      res := lp;
end thread

process idm \in Nodes
variable lpS = 10, resS = 1;
begin
   BeforeS:
	      lpS := lpS + 1;
   SdrS:
        call f(lpS);
	 AfterS:
	      resS := lpS;
end thread

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
		"compare_path": "compile",
		"compare_to": "test_procedures_process/Procedures2p1tC.tla"
}
