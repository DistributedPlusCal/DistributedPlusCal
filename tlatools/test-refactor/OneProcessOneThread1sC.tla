------------------------ MODULE OneProcessOneThread1sC -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid = "ID" )
{
    One:
        found := TRUE;
				x := ar[0];
        i := i + 1;
				ar[i] := 0;
}

}
*)
=============================================================================
