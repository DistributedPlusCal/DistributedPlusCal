------------------------ MODULE NProcesses2ThreadsNoStutteringC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy {
    variables i = 1;
    process (pid \in 1..2)
    {
            i := i + 1;
    }
    {
        while (TRUE) {
            i := i + 2;
        }
    }

    process(qid \in 3..4)
    {
            i := i + 3;
    }
    {
            i := i + 4;
    }

    process(sid = 5)
    {
            i := i + 5;
    }
    {
            i := i + 6;
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "1f77a6cf" /\ chksum(tla) = "6e56185e")
VARIABLES i, pc

vars == << i, pc >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [self \in ProcSet |->  CASE self \in 1..2 -> 1..2
                                     []   self \in 3..4 -> 1..2
                                     []   self = 5 -> 1..2 ]

Init == (* Global variables *)
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> <<"Lbl_1","Lbl_2">>
                                        [] self \in 3..4 -> <<"Lbl_3","Lbl_4">>
                                        [] self = 5 -> <<"Lbl_5","Lbl_6">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 1
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

pid_thread_1(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ i' = i + 2
               /\ pc' = [pc EXCEPT ![self][2] = "Lbl_2"]

pid_thread_2(self) == Lbl_2(self)

pid(self) == pid_thread_1(self) \/ pid_thread_2(self)

Lbl_3(self) == /\ pc[self][1]  = "Lbl_3"
               /\ i' = i + 3
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

qid_thread_1(self) == Lbl_3(self)

Lbl_4(self) == /\ pc[self][2]  = "Lbl_4"
               /\ i' = i + 4
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

qid_thread_2(self) == Lbl_4(self)

qid(self) == qid_thread_1(self) \/ qid_thread_2(self)

Lbl_5 == /\ pc[5][1]  = "Lbl_5"
         /\ i' = i + 5
         /\ pc' = [pc EXCEPT ![5][1] = "Done"]

sid_thread_1 == Lbl_5

Lbl_6 == /\ pc[5][2]  = "Lbl_6"
         /\ i' = i + 6
         /\ pc' = [pc EXCEPT ![5][2] = "Done"]

sid_thread_2 == Lbl_6

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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoStutteringC.tla"
}
