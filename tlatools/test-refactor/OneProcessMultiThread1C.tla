------------------------ MODULE OneProcessMultiThread1C  -------------------------
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


process ( pid2 = 1 )
variable c = 1;
{
    Three:
       x := ar[1];
			 c := c+1;
}
{
    Four:
       ar[i] := 0;
}

}
*)
=============================================================================
