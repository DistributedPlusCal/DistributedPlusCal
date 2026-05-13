------------------------ MODULE NoProcessTwoLabelsPCAL -------------------------
EXTENDS Naturals, TLC

CONSTANT N      (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

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
				x := ar[1];
		Two: 
        i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c7f3ba56" /\ chksum(tla) = "fd4529c6")
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = "One"

One == /\ pc = "One"
       /\ found' = TRUE
       /\ x' = ar[1]
       /\ pc' = "Two"
       /\ UNCHANGED << ar, i >>

Two == /\ pc = "Two"
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ pc' = "Done"
       /\ UNCHANGED << x, found >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One \/ Two
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
