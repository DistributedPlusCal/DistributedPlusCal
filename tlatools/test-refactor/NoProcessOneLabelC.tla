------------------------ MODULE NoProcessOneLabelC -------------------------
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

{
    One:
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7eea8acfea0094f533f8fa4ac2509a08
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
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == One
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-82251ddae25bcf919a43eaf419e31107
=============================================================================
