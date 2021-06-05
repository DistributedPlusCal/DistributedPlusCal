------------------------ MODULE NoProcessTwoLabelsP -------------------------
EXTENDS Naturals, TLC

CONSTANT N      (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;
begin
    One:
        found := TRUE;
				x := ar[0];
		Two: 
        i := i + 1;
				ar[i] := 0;
end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2eb4ed42be23ac3e8ad59a0215351cd4
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
       /\ pc' = "Two"
       /\ UNCHANGED << ar, i >>

Two == /\ pc [1] = "Two"
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ pc' = "Done"
       /\ UNCHANGED << x, found >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One \/ Two
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9e45c3418e732487e2bc9d01e6658125

=============================================================================
