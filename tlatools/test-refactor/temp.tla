------------------------ MODULE temp  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {

process ( pid2 \in 1..2 )
variable c = 1;
{
    Three:
			 c := c+1;
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ae573f7417eedc5178135a23d77236fc
VARIABLES pc, c

vars == << pc, c >>

ProcSet == (1..2)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Process pid2 *)
        /\ c = [self \in 1..2 |-> 1]
        /\ pc = [self \in ProcSet |-> <<"Three">>]

Three(self) == /\ pc[self][1]  = "Three"
               /\ c' = [c EXCEPT ![self] = c[self]+1]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

pid2(self) == Three(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: pid2(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : \A subprocess \in SubProcSet[self] : WF_vars(pid2(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9c16ffd6b06bb4240687ad6b682fb8f8

================================================================================
