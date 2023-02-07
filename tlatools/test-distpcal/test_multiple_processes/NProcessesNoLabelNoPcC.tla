------------------------ MODULE NProcessesNoLabelNoPcC.tla -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables i = 1;
    process (pid \in [0..3])
    {
        while(TRUE) {
            i := i + 1;
        }
    }
    {
        while(TRUE) {
            i := i + 1;
        }
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "d565ddae" /\ chksum(tla) = "e2cbe90a")
VARIABLE i

vars == << i >>

ProcSet == ([0..3])

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ i = 1

pid(self) == i' = i + 1

pid(self) == i' = i + 1

Next == (\E self \in [0..3]: pid(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in [0..3] : \A subprocess \in SubProcSet[self] : WF_vars(pid(self))

\* END TRANSLATION 


=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
}
