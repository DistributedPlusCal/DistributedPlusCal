------------------------ MODULE SequentialSendC -------------------------
EXTENDS Naturals, TLC


(* PlusCal options (-distpcal) *)

(* --algorithm transfer {

channel c;

{
    A: send(c, 2);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-fa8c13ba94e3d6e6c5a1eee98d3601fa
VARIABLES c, pc

vars == << c, pc >>

Init == (* Global variables *)
        /\ c = {}
        /\ pc = "A"

A == /\ pc = "A"
     /\ c' = (c \cup {2})
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e5c70a98f7a9f702d297184bdc340106

==========================================================
