------------------------ MODULE SequentialSendC -------------------------
EXTENDS Naturals, TLC


(* PlusCal options (-distpcal) *)

(* --algorithm transfer {

variables x = 2;
channel c;

{
    A: 
    	x := x + 1;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-fb19528c0c9994e982adc3b9d849190e
VARIABLES x, c, pc

vars == << x, c, pc >>

Init == (* Global variables *)
        /\ x = 2
        /\ c = {}
        /\ pc = "A"

A == /\ pc [1] = "A"
     /\ x' = x + 1
     /\ pc' = "Done"
     /\ c' = c

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-db75a0a452a201eb6f550334da908860

==========================================================
