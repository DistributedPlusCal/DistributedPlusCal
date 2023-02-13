------------------------ MODULE NProcesses2ThreadsNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy {
    variables i = 1;
    fair process (pid \in 1..2)
    {
        i := i + 1;
        i := i + 10;
    }
    {
        i := i + 2;
        i := i + 20;
    }

    process(qid \in 3..4)
    {
            i := i + 3;
    }
    {
            i := i + 4;
    }

    fair process(sid = 5)
    {
        i := i + 5;
        i := i + 50;
    }
    {
        i := i + 6;
        i := i + 60;
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "ccc72039" /\ chksum(tla) = "c7e747a2")
VARIABLES i, pc

vars == << i, pc >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 1..2 THEN 1..2
                                 ELSE IF _n1 \in 3..4 THEN 1..2
                                    ELSE (**5**) 1..2]

Init == (* Global variables *)
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> <<"Lbl_1","Lbl_3">>
                                        [] self \in 3..4 -> <<"Lbl_5","Lbl_6">>
                                        [] self = 5 -> <<"Lbl_7","Lbl_9">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 1
               /\ pc' = [pc EXCEPT ![self][1] = "Lbl_2"]

Lbl_2(self) == /\ pc[self][1]  = "Lbl_2"
               /\ i' = i + 10
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

pid1(self) == Lbl_1(self) \/ Lbl_2(self)

Lbl_3(self) == /\ pc[self][2]  = "Lbl_3"
               /\ i' = i + 2
               /\ pc' = [pc EXCEPT ![self][2] = "Lbl_4"]

Lbl_4(self) == /\ pc[self][2]  = "Lbl_4"
               /\ i' = i + 20
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

pid2(self) == Lbl_3(self) \/ Lbl_4(self)

pid(self) == pid1(self) \/ pid2(self)

Lbl_5(self) == /\ pc[self][1]  = "Lbl_5"
               /\ i' = i + 3
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

qid1(self) == Lbl_5(self)

Lbl_6(self) == /\ pc[self][2]  = "Lbl_6"
               /\ i' = i + 4
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]

qid2(self) == Lbl_6(self)

qid(self) == qid1(self) \/ qid2(self)

Lbl_7 == /\ pc[5][1]  = "Lbl_7"
         /\ i' = i + 5
         /\ pc' = [pc EXCEPT ![5][1] = "Lbl_8"]

Lbl_8 == /\ pc[5][1]  = "Lbl_8"
         /\ i' = i + 50
         /\ pc' = [pc EXCEPT ![5][1] = "Done"]

sid1 == Lbl_7 \/ Lbl_8

Lbl_9 == /\ pc[5][2]  = "Lbl_9"
         /\ i' = i + 6
         /\ pc' = [pc EXCEPT ![5][2] = "Lbl_10"]

Lbl_10 == /\ pc[5][2]  = "Lbl_10"
          /\ i' = i + 60
          /\ pc' = [pc EXCEPT ![5][2] = "Done"]

sid2 == Lbl_9 \/ Lbl_10

sid == sid1 \/ sid2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in 1..2: pid(self))
           \/ (\E self \in 3..4: qid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(pid(self))
        /\ WF_vars(sid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoPcC.tla"
}
