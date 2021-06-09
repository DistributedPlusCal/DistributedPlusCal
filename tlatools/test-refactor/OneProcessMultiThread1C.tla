------------------------ MODULE OneProcessMultiThread1C  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;


process ( pid2 = 1 )
{
    Three:
       x := ar[1];
}
{
    Four:
       ar[i] := 0;
}

}
*)
=============================================================================
