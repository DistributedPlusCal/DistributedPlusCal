------------------------ MODULE OneProcessOneThread1C -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid = 1 )
variables c = 3;
{
    One:
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
				c := c+1;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a7d20ad799e509a5794875c825632805
VARIABLES ar, x, found, i, pc, c

vars == << ar, x, found, i, pc, c >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = 3
        /\ pc = [self \in ProcSet |-> <<"One">>]

One == /\ pc[1][1]  = "One"
       /\ found' = TRUE
       /\ x' = ar[1]
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ c' = c+1
       /\ pc' = [pc EXCEPT ![1][1] = "Done"]

pid == One

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b1e4950aa03129d671f9f71f290fea5c
=============================================================================
