------------------------ MODULE TwoProcessesOneThread2C  -------------------------
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

process ( pid2 = 1 )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-36ef000b267eafc1b0e33fb26223becd
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (PROCSet) \cup {1}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in PROCSet THEN 1..1
                                   ELSE (**1**) 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in PROCSet -> <<"One">>
                                        [] self = 1 -> <<"Three">>]

One(self) == /\ pc[self][1]  = "One"
             /\ found' = TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, x, i >>

Two(self) == /\ pc[self][1]  = "Two"
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << ar, x, found >>

pid1(self) == One(self) \/ Two(self)

Three == /\ pc[1][1]  = "Three"
         /\ x' = ar[1]
         /\ pc' = [pc EXCEPT ![1][1] = "Four"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc[1][1]  = "Four"
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

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : \A subprocess \in SubProcSet[self] : WF_vars(pid1(self))
        /\ WF_vars(pid2)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-bdbfa90c0c077ec8e6675284d3287048
=============================================================================
