------------------------ MODULE TwoProcessesOneThread2sC  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
CONSTANT PROCSet     (* Set of process indexes *)

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

process ( pid2 = "IDone" )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

process ( pid3 = 2 )
{
    Five:
				x := ar[1];
	  Six:
				ar[i] := 0;
}

}
*)
=============================================================================
