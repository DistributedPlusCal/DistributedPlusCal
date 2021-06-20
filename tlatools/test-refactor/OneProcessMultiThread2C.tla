------------------------ MODULE OneProcessMultiThread2C  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-distpcal) *)
(* PlusCal options (-termination) *)

(*--algorithm Dummy {

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in PROCSet )
{
    One:
       found := TRUE;
}
{
    Two:
       i := i + 1;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-20d30c04dd2e0b146f23d9de48dcb1aa
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (PROCSet)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"One","Two">>]

One(self) == /\ pc[self][1]  = "One"
             /\ found' = TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << ar, x, i >>

Two(self) == /\ pc[self][2]  = "Two"
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]
             /\ UNCHANGED << ar, x, found >>

pid1(self) == One(self) \/ Two(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid1(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1e563bbba6fbf3aaaafbd06b722eb705
=============================================================================
