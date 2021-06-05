------------------------ MODULE OneProcessOneThread2nC -------------------------
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

process ( pid \in PROCSet )
{
    One:
        found := TRUE;
				x := ar[0];
	  Two:
				i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-10c63226511f05432349e49abf1887d8
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (PROCSet)

SubProcSet == [n \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"One">>]

One(self) == /\ pc[self] [1] = "One"
             /\ found' = TRUE
             /\ x' = ar[0]
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, i >>

Two(self) == /\ pc[self] [1] = "Two"
             /\ i' = i + 1
             /\ ar' = [ar EXCEPT ![i'] = 0]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << x, found >>

pid(self) == One(self) \/ Two(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-cfcb0ef20207115470c109f9d4ac6b8f

=============================================================================
