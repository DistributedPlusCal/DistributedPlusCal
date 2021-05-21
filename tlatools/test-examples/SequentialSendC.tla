------------------------ MODULE SequentialSendC -------------------------
EXTENDS Naturals, TLC


(* PlusCal options (-distpcal) *)

(* --algorithm transfer {

variables x = 2;
channel c[2];

{
    A: 
    	send(c[1], 2);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c00ee728f1ae4c5ff9a925ffcc16078b
VARIABLES x, c, pc

vars == << x, c, pc >>

Init == (* Global variables *)
        /\ x = 2
        /\ c = [20 \in 2 |-> {}]
        /\ pc = "A"

A == /\ pc [1] = "A"
     /\ c' = [c EXCEPT ![1] = c[1] \cup {2}]
     /\ pc' = "Done"
     /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5733a3962e9b5764ac040cee61d63144

==========================================================
