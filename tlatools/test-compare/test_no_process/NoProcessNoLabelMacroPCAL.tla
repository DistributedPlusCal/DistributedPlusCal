------------------------ MODULE NoProcessNoLabelMacroPCAL -------------------------
EXTENDS Naturals, TLC, Sequences

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      

(* PlusCal options (-termination) *)

(*--algorithm Dummy {

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1,
		r = 9;

macro inc(i,inc) {
    ar[i] := inc;
    i := i+1;
}

{
				found := TRUE;
				x := ar[1];
				i := i + 1;
				ar[i] := 0;
				inc(x,1);
				inc(i,1);
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9e876c68" /\ chksum(tla) = "6d5f9d4f")
VARIABLES ar, x, found, i, r, pc

vars == << ar, x, found, i, r, pc >>

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ r = 9
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ found' = TRUE
         /\ x' = ar[1]
         /\ i' = i + 1
         /\ ar' = [ar EXCEPT ![i'] = 0]
         /\ pc' = "Lbl_2"
         /\ r' = r

Lbl_2 == /\ pc = "Lbl_2"
         /\ ar' = [ar EXCEPT ![x] = 1]
         /\ x' = x+1
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << found, i, r >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ ar' = [ar EXCEPT ![i] = 1]
         /\ i' = i+1
         /\ pc' = "Done"
         /\ UNCHANGED << x, found, r >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================

