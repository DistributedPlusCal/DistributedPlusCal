------------------------ MODULE Procedures1p1tRecP -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
N == 5
\* ASSUME N \in Nat 
\* Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy 
variable c = 0,
         acc = [i \in 0 .. N |-> 0];

procedure fact(n,res)
begin
  Start:
	  acc[n] := res;
    if  n = 0  then
        c := res;
        return;
    else 
        res := res * ( n-1 );
        call fact(n-1, res);
    end if;
  End:
	  return;
end procedure

process id = 2
variable lp = 3;
begin
   Before:
	      lp := lp + 1;
   Sdr:
        call fact(lp,1);
	 After:
	      skip;
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
		"compare_to": "test_procedures_process/Procedures1p1tRecC.tla"
}
