------------------------ MODULE OneProcessMultiThread1P  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 

variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;


process pid = 1
begin
    Three:
       x := ar[1];
end process;
begin
    Four:
       ar[i] := 0;
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-196537c751efc8159203c11d5d693b37
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"Three","Four">>]

Three == /\ pc[1][1]  = "Three"
         /\ x' = ar[1]
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc[1][2]  = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![1][2] = "Done"]
        /\ UNCHANGED << x, found, i >>

pid == Three \/ Four

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-844a4cf278c6972e4735ffb7eb015eac
=============================================================================
