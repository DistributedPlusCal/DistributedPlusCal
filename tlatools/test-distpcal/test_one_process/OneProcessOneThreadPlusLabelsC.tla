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
\* BEGIN TRANSLATION (chksum(pcal) = "369dc761" /\ chksum(tla) = "f155786a")
VARIABLES found, i, pc, c

vars == << found, i, pc, c >>

ProcSet == (PROCSet)

Init == (* Global variables *)
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = [self \in PROCSet |-> 3]
        /\ pc = [self \in ProcSet |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ found' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << i, c >>

L2(self) == /\ pc[self] = "L2"
            /\ i' = i + 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << found, c >>

pid(self) == L1(self) \/ L2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : WF_vars((pc[self] # "L2") /\ pid(self)) /\ SF_vars(L1(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}
