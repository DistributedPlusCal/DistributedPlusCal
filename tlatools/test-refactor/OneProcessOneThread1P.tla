------------------------ MODULE OneProcessOneThread1P -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 

variables 
    i = 1;

process pid = 1
begin
    i := i + 1;
end process

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3cfa086badba724d2789ec7f7c29c6b7
VARIABLES i, pc

vars == << i, pc >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"Lbl_1">>]

Lbl_1 == /\ pc[1][1]  = "Lbl_1"
         /\ i' = i + 1
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

pid == Lbl_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6e74c9a4ef21b9bbf664c133ec853770

=============================================================================
