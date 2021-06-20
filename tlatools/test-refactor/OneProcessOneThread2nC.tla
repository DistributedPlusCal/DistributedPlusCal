------------------------ MODULE OneProcessOneThread2nC -------------------------
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

process ( pid \in PROCSet )
variables c = 3;
{
    One:
        found := TRUE;
				x := ar[1];
				c := c+1;
	  Two:
				i := i + 1;
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-5627cd3f867a40f3ac50a08f992f61bb
VARIABLES ar, x, found, i, pc, c

vars == << ar, x, found, i, pc, c >>

ProcSet == (PROCSet)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = [self \in PROCSet |-> 3]
        /\ pc = [self \in ProcSet |-> <<"One">>]

One(self) == /\ pc[self][1]  = "One"
             /\ found' = TRUE
             /\ x' = ar[1]
             /\ c' = [c EXCEPT ![self] = c[self]+1]
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, i >>

Two(self) == /\ pc[self][1]  = "Two"
             /\ i' = i + 1
             /\ ar' = [ar EXCEPT ![i'] = 0]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << x, found, c >>

pid(self) == One(self) \/ Two(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : \A subprocess \in SubProcSet[self] : WF_vars(pid(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-26d882f9fa52210086698506bdb1b7b7
=============================================================================
