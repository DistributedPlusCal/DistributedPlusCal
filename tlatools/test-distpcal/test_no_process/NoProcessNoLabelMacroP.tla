------------------------ MODULE NoProcessNoLabelMacroP -------------------------
EXTENDS Naturals, TLC, Sequences

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1,
		r = 9;

macro inc(i,inc)
begin
    ar[i] := inc;
    i := i+1;
end macro

begin
				found := TRUE;
				x := ar[1];
				i := i + 1;
				ar[i] := 0;
				inc(x,1);
				inc(i,1);
end algorithm
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 4,
        "MAXINT": 4
		},
    "do_compare": true,
    "compare_to": "test_no_process/NoProcessNoLabelMacroPCAL.tla"
}
