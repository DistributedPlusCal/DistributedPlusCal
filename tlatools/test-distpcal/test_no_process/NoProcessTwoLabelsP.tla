------------------------ MODULE NoProcessTwoLabelsP -------------------------
EXTENDS Naturals, TLC

CONSTANT N      (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;
begin
    One:
        found := TRUE;
				x := ar[1];
		Two: 
        i := i + 1;
				ar[i] := 0;
end algorithm;
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
    "compare_to": "test_no_process/NoProcessTwoLabelsPCAL.tla"
}
