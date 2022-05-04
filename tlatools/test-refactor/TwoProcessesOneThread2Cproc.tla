------------------------ MODULE TwoProcessesOneThread2Cproc  -------------------------
EXTENDS Naturals, TLC

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 3
\* CONSTANT PROCSet     (* Set of process indexes *)
PROCSet == 1 .. 2     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in PROCSet )
{
    One:
        found := TRUE;
	  Two:
				i := i + 1;
}

process ( pid2 = 1 )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

}
*)
=============================================================================
