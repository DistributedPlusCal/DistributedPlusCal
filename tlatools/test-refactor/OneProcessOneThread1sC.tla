------------------------ MODULE OneProcessOneThread1sC -------------------------
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

process ( pid = "ID" )
{
    One:
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-803f7c4486e040bdeca441f652564c11
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == {"ID"}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"One">>]

One == /\ pc["ID"][1]  = "One"
       /\ found' = TRUE
       /\ x' = ar[1]
       /\ i' = i + 1
       /\ ar' = [ar EXCEPT ![i'] = 0]
       /\ pc' = [pc EXCEPT !["ID"][1] = "Done"]

pid == One

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2189d6b81ec2e9ecbb0725cdc4824d13
=============================================================================
