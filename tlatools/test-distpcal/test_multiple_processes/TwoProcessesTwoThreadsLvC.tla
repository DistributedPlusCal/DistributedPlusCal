------------------------ MODULE TwoProcessesTwoThreadsLvC  -------------------------
EXTENDS Naturals, TLC

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 2
\* CONSTANT PROCSet     (* Set of process indexes *)
PROCSet == 2..3
(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in PROCSet )
variables lvpid1 = 0;
{
    found := TRUE;
	i := i + 1;
    lvpid1 := i;
}
{
    found := TRUE;
	i := i + 1;
    lvpid1 := i;
}

process ( pid2 = 1 )
variables lvpid2 = 10;
{
	x := ar[1];
	ar[i] := 0;
    lvpid2 := x;
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
    "compare_to": "test_multiple_processes/TwoProcessesTwoThreadsLvC.tla"
}
