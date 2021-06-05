------------------------ MODULE NoProcessOneLabelC -------------------------
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

{
    One:
        found := TRUE;
				x := ar[0];
        i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bedef6f350f0c68f046a67df8d759205
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = "One"

One == /\ pc [1] = "One"
       /\ found' = TRUE
       /\ x' = ar[0]
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ff55bddb3032e4c877a99f4bb4a0a8b1

=============================================================================
