------------------------ MODULE TwoProcessesOneThread2C  -------------------------
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
	  Two:
				i := i + 1;
}

process ( pid2 = 1 )
{
    Three:
				x := ar[0];
	  Four:
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a95d60e97cee22c5bd66058749aad91f
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (PROCSet) \cup {1}

SubProcSet == [n \in ProcSet |-> IF n \in PROCSet THEN 1
                             ELSE (**1**) 1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in PROCSet -> <<"One">>
                                        [] self = 1 -> <<"Three">>]

One(self) == /\ pc[self] [1] = "One"
             /\ found' = TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, x, i >>

Two(self) == /\ pc[self] [1] = "Two"
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << ar, x, found >>

pid1(self) == One(self) \/ Two(self)

Three == /\ pc[1] [1] = "Three"
         /\ x' = ar[0]
         /\ pc' = [pc EXCEPT ![1][1] = "Four"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc[1] [1] = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![1][1] = "Done"]
        /\ UNCHANGED << x, found, i >>

pid2 == Three \/ Four

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid2
           \/ (\E self \in PROCSet: pid1(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-08ce95a7e4e8e17b42c39618accb3e60

=============================================================================
