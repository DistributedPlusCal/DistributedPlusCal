------------------------ MODULE OneProcessOneThread2C -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy {

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid = 1 )
{
    One:
        found := TRUE;
				x := ar[1];
	  Two:
				i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-50a4345fc1d487f7dbad3fa7df57abce
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"One">>]

One == /\ pc[1][1]  = "One"
       /\ found' = TRUE
       /\ x' = ar[1]
       /\ pc' = [pc EXCEPT ![1][1] = "Two"]
       /\ UNCHANGED << ar, i >>

Two == /\ pc[1][1]  = "Two"
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ pc' = [pc EXCEPT ![1][1] = "Done"]
       /\ UNCHANGED << x, found >>

pid == One \/ Two

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-734a5a31a90f2edf1794125c4f78c29c
=============================================================================
