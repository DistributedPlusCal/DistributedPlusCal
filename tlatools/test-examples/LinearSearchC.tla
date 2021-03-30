------------------------ MODULE LinearSearchC -------------------------
EXTENDS Naturals, TLC

CONSTANT N      (* Size of arrays *)
CONSTANT MAXINT (* Max integer value *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm LinearSearch {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,              (* Value to find *)
    found = FALSE,
    i = 1;

{
    Loop:
    while ( i <= N /\ ~found ) {
        found := ar[i]=x;
        i := i + 1;
    } ;
        
    FinalCheck:
    assert ( found <=> (\E j \in 1..N : ar[j] = x) )      
}

}
*)

==========================================================
