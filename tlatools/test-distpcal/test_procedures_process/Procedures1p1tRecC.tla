------------------------ MODULE Procedures1p1tRecC -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
N == 5
\* ASSUME N \in Nat 
\* Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy {
variable c = 0,
         acc = [i \in 0 .. N |-> 0];

procedure fact(n,res) {
  Start:
	  acc[n] := res;
    if ( n = 0 ) {
        c := res;
        return;
    }
    else {
        res := res * ( n-1 );
        call fact(n-1, res);
    };
  End:
	  return;
}

process (id = 2)
variable lp = 3;
{
   Before:
	      lp := lp + 1;
   Sdr:
        call fact(lp,1);
	 After:
	      skip;
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
