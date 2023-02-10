------------------------ MODULE NProcessesNoLabelNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy {
    variables i = 1;
    process (pid \in 1..2)
    {
        while (TRUE) {
            i := i + 1;
        }
    }

    process(qid \in 3..4)
    {
        while(TRUE) {
            i := i + 3;
        }
    }

    process(sid = 5)
    {
        while(TRUE) {
            i := i + 5;
        }
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "5ffc6afe" /\ chksum(tla) = "a93fbf1")
VARIABLE i

vars == << i >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 1..2 THEN 1..1
                                 ELSE IF _n1 \in 3..4 THEN 1..1
                                    ELSE (**5**) 1..1]

Init == (* Global variables *)
        /\ i = 1

pid1(self) == i' = i + 1

pid(self) == pid1(self)

qid1(self) == i' = i + 3

qid(self) == qid1(self)

sid1 == i' = i + 5

sid == sid1

Next == sid
           \/ (\E self \in 1..2: pid(self))
           \/ (\E self \in 3..4: qid(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_multiple_processes/NProcessesNoLabelNoPcC.tla"
}
