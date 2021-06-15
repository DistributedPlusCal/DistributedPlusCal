------------------------ MODULE OneProcessOneThread2nC -------------------------
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

process ( pid \in PROCSet )
variables c = 3;
{
    One:
        found := TRUE;
				x := ar[1];
				c := c+1;
	  Two:
				i := i + 1;
				ar[i] := 0;
}

}
*)
=============================================================================
