------------------------ MODULE NoProcessNoLabelC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

variables 
    i = 1;
    
{
        i := i + 1;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-609321c9a4e56d24bbd6d8c8e52f2f34
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-34b2a2fea3f725c7a72ae0bb10816876
=============================================================================
