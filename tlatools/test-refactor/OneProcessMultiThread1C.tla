------------------------ MODULE OneProcessMultiThread1C  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;


process ( pid2 = 1 )
{
    Three:
       x := ar[0];
}
{
    Four:
       ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c096e574ed6add121a270a94f13af395
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == {1}

SubProcSet == [n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"Three","Four">>]

Three == /\ pc[1] [1] = "Three"
         /\ x' = ar[0]
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc[1] [2] = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![1][2] = "Done"]
        /\ UNCHANGED << x, found, i >>

pid2 == Three \/ Four

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2f0d1a30e3473cd453ed37fbb0ca1f55

=============================================================================
