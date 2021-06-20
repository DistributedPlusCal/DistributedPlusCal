------------------------ MODULE NoProcessEmptyBodyP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 

variables 
    i = 1;

begin
end algorithm;

*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-5d8261786d2a315c974f7e2a49241eea
VARIABLE i

vars == << i >>

Init == (* Global variables *)
        /\ i = 1

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0d33d5bf94a1bbb6a1056a15a1c051ed
=============================================================================
