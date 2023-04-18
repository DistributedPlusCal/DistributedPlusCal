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
\* BEGIN TRANSLATION (chksum(pcal) = "caf63b52" /\ chksum(tla) = "b6ddfd07")
VARIABLES i, pc

vars == << i, pc >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 1..2 THEN 1..2
                                 ELSE IF _n1 \in 3..4 THEN 1..2
                                    ELSE (**5**) 1..2]

Init == (* Global variables *)
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> <<"Lbl_1","Lbl_2">>
                                        [] self \in 3..4 -> <<"Lbl_3","Lbl_4">>
                                        [] self = 5 -> <<"Lbl_5","Lbl_6">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 1
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

pid1(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ i' = i + 2
               /\ pc' = [pc EXCEPT ![self][2] = "Lbl_2"]

pid2(self) == Lbl_2(self)

pid(self) == pid1(self) \/ pid2(self)

Lbl_3(self) == /\ pc[self][1]  = "Lbl_3"
               /\ i' = i + 3
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

qid1(self) == Lbl_3(self)

Lbl_4(self) == /\ pc[self][2]  = "Lbl_4"
               /\ i' = i + 4
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

qid2(self) == Lbl_4(self)

qid(self) == qid1(self) \/ qid2(self)

Lbl_5 == /\ pc[5][1]  = "Lbl_5"
         /\ i' = i + 5
         /\ pc' = [pc EXCEPT ![5][1] = "Done"]

sid1 == Lbl_5

Lbl_6 == /\ pc[5][2]  = "Lbl_6"
         /\ i' = i + 6
         /\ pc' = [pc EXCEPT ![5][2] = "Done"]

sid2 == Lbl_6

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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoStutteringC.tla"
}
