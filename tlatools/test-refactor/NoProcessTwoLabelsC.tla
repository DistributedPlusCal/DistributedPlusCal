------------------------ MODULE NoProcessOneLabelC -------------------------
EXTENDS Naturals, TLC

CONSTANT N      (* Size of arrays *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

{
    One:
        found := TRUE;
				x := ar[0];
		Two: 
        i := i + 1;
				ar[i] := 0;
}

}
*)
