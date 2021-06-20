------------------------ MODULE TwoProcessesOneThread2sC  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

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

process ( pid2 = "IDone" )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

process ( pid3 = 2 )
{
    Five:
				x := ar[1];
	  Six:
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-5ba77cc5deb177e14049d96dbe7869ac
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (PROCSet) \cup {"IDone"} \cup {2}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in PROCSet THEN 1..1
                                   ELSE IF _n42 = "\"", "IDone", "\"" THEN 1..1
                                     ELSE (**2**) 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in PROCSet -> <<"One">>
                                        [] self = "IDone" -> <<"Three">>
                                        [] self = 2 -> <<"Five">>]

One(self) == /\ pc[self][1]  = "One"
             /\ found' = TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, x, i >>

Two(self) == /\ pc[self][1]  = "Two"
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << ar, x, found >>

pid1(self) == One(self) \/ Two(self)

Three == /\ pc["IDone"][1]  = "Three"
         /\ x' = ar[1]
         /\ pc' = [pc EXCEPT !["IDone"][1] = "Four"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc["IDone"][1]  = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT !["IDone"][1] = "Done"]
        /\ UNCHANGED << x, found, i >>

pid2 == Three \/ Four

Five == /\ pc[2][1]  = "Five"
        /\ x' = ar[1]
        /\ pc' = [pc EXCEPT ![2][1] = "Six"]
        /\ UNCHANGED << ar, found, i >>

Six == /\ pc[2][1]  = "Six"
       /\ ar' = [ar EXCEPT ![i] = 0]
       /\ pc' = [pc EXCEPT ![2][1] = "Done"]
       /\ UNCHANGED << x, found, i >>

pid3 == Five \/ Six

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid2 \/ pid3
           \/ (\E self \in PROCSet: pid1(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : \A subprocess \in SubProcSet[self] : WF_vars(pid1(self))
        /\ WF_vars(pid2)
        /\ WF_vars(pid3)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e7bb5f27c658a5991f171a340be1bc7b
=============================================================================
