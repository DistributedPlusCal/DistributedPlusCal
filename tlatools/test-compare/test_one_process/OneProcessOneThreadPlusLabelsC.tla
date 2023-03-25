------------------------ MODULE OneProcessOneThreadPlusLabelsC -------------------------
EXTENDS Naturals, TLC

PROCSet == 1..2

(* PlusCal options (-distpcal) *)

(*--algorithm Dummy {
variables 
    found = FALSE,
    i = 1;

fair process ( pid \in PROCSet )
variables c = 3;
{
    L1:+
        found := TRUE;
    L2:-
        i := i + 1;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3d26ec56" /\ chksum(tla) = "5d990621")
VARIABLES found, i, pc, c

vars == << found, i, pc, c >>

ProcSet == (PROCSet)

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = [self \in PROCSet |-> 3]
        /\ pc = [self \in ProcSet |-> <<"L1">>]

L1(self) == /\ pc[self][1]  = "L1"
            /\ found' = TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "L2"]
            /\ UNCHANGED << i, c >>

L2(self) == /\ pc[self][1]  = "L2"
            /\ i' = i + 1
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ UNCHANGED << found, c >>

pid1(self) == L1(self) \/ L2(self)

pid(self) == pid1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : WF_vars((pc[self][1] # "L2") /\ pid1(self)) /\ SF_vars(L1(self))

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}
