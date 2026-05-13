------------------------ MODULE OneProcessOneThreadPlusLabelsC -------------------------
EXTENDS Naturals, TLC

PROCSet == 1..2

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
\* BEGIN TRANSLATION (chksum(pcal) = "de87c50e" /\ chksum(tla) = "25445210")
VARIABLES pc, found, i, c

vars == << pc, found, i, c >>

ProcSet == (PROCSet)

SubProcSet == [self \in ProcSet |-> 1..1]

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

pid_thread_1(self) == L1(self) \/ L2(self)

pid(self) == pid_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : /\ WF_vars((pc[self][1] # "L2") /\ pid_thread_1(self))
                                 /\ SF_vars(L1(self))

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_to": ""
}
