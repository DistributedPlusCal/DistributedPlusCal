------------------------ MODULE NoProcessNoLabelMacroC -------------------------
EXTENDS Naturals, TLC, Sequences

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1,
		r = 9;

macro inc(i,inc) {
    ar[i] := inc;
    i := i+1;
}

{
				found := TRUE;
				x := ar[1];
				i := i + 1;
				ar[i] := 0;
				inc(x,1);
				inc(i,1);
}

}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 3
		},
    "compare_to": "test_no_process/NoProcessNoLabelMacroPCAL.tla"
}
