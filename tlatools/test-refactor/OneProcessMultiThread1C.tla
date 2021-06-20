------------------------ MODULE OneProcessMultiThread1C  -------------------------
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


process ( pid2 = 1 )
variable c = 1;
{
    Three:
       x := ar[1];
			 c := c+1;
}
{
    Four:
       ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b00a0926e06c39fcf585316cc491b622
VARIABLES ar, x, found, i, pc, c

vars == << ar, x, found, i, pc, c >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid2 *)
        /\ c = 1
        /\ pc = [self \in ProcSet |-> <<"Three","Four">>]

Three == /\ pc[1][1]  = "Three"
         /\ x' = ar[1]
         /\ c' = c+1
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc[1][2]  = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![1][2] = "Done"]
        /\ UNCHANGED << x, found, i, c >>

pid2 == Three \/ Four

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid2)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-abc9502cc26a9f3ae7964a3bbafdbc8a
=============================================================================
