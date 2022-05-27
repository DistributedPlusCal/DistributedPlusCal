------------------------ MODULE Procedures2p1tPalt -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT Nodes     (* Set of process indexes *)
Nodes == 1 .. N
 
(*
--algorithm Dummy 
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
end process

process idm \in Nodes
variable lp = 10, res = 1;
begin
   BeforeS:
	      lp := lp + 1;
   SdrS:
        call f(lp);
	 AfterS:
	      res := lp;
end process

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
		"compare_to": "test_procedures_process/Procedures2p1tCalt.tla"
}
