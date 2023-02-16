------------------------ MODULE TwoProcessesOneThread2sC  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
\* CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..3,               
    found = FALSE,
    i = 1;

process ( pid1 \in  {"P1", "P2"} )
{
    One:
        found := TRUE;
	  Two:
				i := i + 1;
}

process ( pid2 = "P3" )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

process ( pid3 = "P4" )
{
    Five:
				x := ar[1];
	  Six:
				ar[i] := 0;
}

}
*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
		    "N": 2,
		    "MAXINT": 2
	},
    "compare_to": "test_multiple_processes/TwoProcessesOneThread2sC.tla"
}
