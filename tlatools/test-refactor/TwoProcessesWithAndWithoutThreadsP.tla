----------------------------- MODULE TwoProcessesWithAndWithoutThreadsP -----------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P
ASSUME P \in Nat
Processes == 2..P
(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Syntax
variables x = 0;
process p = 1 
begin
     A: x := x+2 ;
end process

process q \in Processes
begin
     C: x := x+1 ;
end process
begin
    D: x := x+1;
end subprocess 

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-27fe6478dbb89f0cf78f6cf3268db695
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {1} \cup (Processes)

SubProcSet == [_n1 \in ProcSet |-> IF _n1 = 1 THEN 1..1
                               ELSE (**Processes**) 1..2]

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self \in Processes -> <<"C","D">>]

A == /\ pc[1][1]  = "A"
     /\ x' = x+2
     /\ pc' = [pc EXCEPT ![1][1] = "Done"]

p == A

C(self) == /\ pc[self][1]  = "C"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![self][1] = "Done"]

D(self) == /\ pc[self][2]  = "D"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![self][2] = "Done"]

q(self) == C(self) \/ D(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == p
           \/ (\E self \in Processes: q(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p)
        /\ \A self \in Processes : \A subprocess \in SubProcSet[self] : WF_vars(q(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4c27402ad515c9fd13eff0377d72ed52
=============================================================================
\* Modification History
\* Last modified Wed May 04 14:02:08 CEST 2022 by cirstea
\* Last modified Wed May 04 12:32:29 GMT 2022 by zunai
\* Created Tue May 03 11:13:21 GMT 2022 by zunai
