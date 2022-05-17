------------------------ MODULE NoProcessNoLabelPCAL -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination) *)

(*--algorithm Dummy {
variables i = 1;
{
        i := i + 1;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "caf5039d" /\ chksum(tla) = "f600c1f5")
VARIABLES i, pc

vars == << i, pc >>

Init == (* Global variables *)
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ i' = i + 1
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
