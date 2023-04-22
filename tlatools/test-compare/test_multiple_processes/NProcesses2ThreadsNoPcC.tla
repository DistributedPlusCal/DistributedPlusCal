------------------------ MODULE NProcesses2ThreadsNoPcC -------------------------
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
    {
        while (TRUE) {
            i := i + 2;
        }
    }

    process(qid \in 3..4)
    {
        while(TRUE) {
            i := i + 3;
        }
    }
    {
        while(TRUE) {
            i := i + 4;
        }
    }

    process(sid = 5)
    {
        while(TRUE) {
            i := i + 5;
        }
    }
    {
        while(TRUE) {
            i := i + 6;
        }
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "d87540eb" /\ chksum(tla) = "4a771cf7")
VARIABLE i

vars == << i >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 1..2 THEN 1..2
                                   ELSE IF _n1 \in 3..4 THEN 1..2
                                   ELSE (** _n1 = 5 **) 1..2]

Init == (* Global variables *)
        /\ i = 1

pid1(self) == i' = i + 1

pid2(self) == i' = i + 2

pid(self) == pid1(self) \/ pid2(self)

qid1(self) == i' = i + 3

qid2(self) == i' = i + 4

qid(self) == qid1(self) \/ qid2(self)

sid1 == i' = i + 5

sid2 == i' = i + 6

sid == sid1 \/ sid2

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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoPcC.tla"
}
