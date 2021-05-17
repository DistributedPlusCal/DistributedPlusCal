------------------------ MODULE LinearSearchP -------------------------
EXTENDS Naturals, TLC

CONSTANT N      (* Size of arrays *)
CONSTANT MAXINT (* Max integer value *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm LinearSearch
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,              (* Value to find *)
    found = FALSE,
    i = 1;

begin

    Loop:
    while i <= N /\ ~found do
        found := ar[i]=x;
        i := i + 1;
    end while;
        
    FinalCheck:
    assert( found <=> (\E j \in 1..N : ar[j] = x) )      

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2c700ef455fabb4d3e15fc0243c2b793
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = "Loop"

Loop == /\ pc [1] = "Loop"
        /\ IF i <= N /\ ~found
              THEN /\ found' = (ar[i]=x)
                   /\ i' = i + 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "FinalCheck"
                   /\ UNCHANGED << found, i >>
        /\ UNCHANGED << ar, x >>

FinalCheck == /\ pc [1] = "FinalCheck"
              /\ Assert(( found <=> (\E j \in 1..N : ar[j] = x) ), 
                        "Failure of assertion at line 26, column 5.")
              /\ pc' = "Done"
              /\ UNCHANGED << ar, x, found, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Loop \/ FinalCheck
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a12ad19f486d5aa6af5d851d10df95d7

==========================================================
