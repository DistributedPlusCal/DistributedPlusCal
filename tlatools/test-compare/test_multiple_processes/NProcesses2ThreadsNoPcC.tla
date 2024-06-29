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
\* BEGIN TRANSLATION (chksum(pcal) = "d87540eb" /\ chksum(tla) = "8061e20a")
VARIABLE i

vars == << i >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [self \in ProcSet |->  CASE self \in 1..2 -> 1..2
                                     []   self \in 3..4 -> 1..2
                                     []   self = 5 -> 1..2 ]

Init == (* Global variables *)
        /\ i = 1

pid_thread_1(self) == i' = i + 1

pid_thread_2(self) == i' = i + 2

pid(self) == pid_thread_1(self) \/ pid_thread_2(self)

qid_thread_1(self) == i' = i + 3

qid_thread_2(self) == i' = i + 4

qid(self) == qid_thread_1(self) \/ qid_thread_2(self)

sid_thread_1 == i' = i + 5

sid_thread_2 == i' = i + 6

sid == sid_thread_1 \/ sid_thread_2

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
