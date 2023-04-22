------------------------ MODULE NProcesses2ThreadsFairnessWfC -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-label -distpcal) *)

PROCSet == 1..2

(*--algorithm Dummy {
    variables
	    x = 4,
 		i = 1;
	
    fair process(qid \in 3..4)
    {
        QPL1:+
            i := i + 31;
        QPL2:+
            i := i + 32;
        QPL:-
            i := i + 4;
    }
    {
        QML:+
            x := 1;
    }

    fair process(sid = 5)
    variables lvqid = 1;
    {
        SPL:+
            x := lvqid;
    }
    {
        SML1:-
            i := i + 61;
        SML2:-
            i := i + 62;
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "1fd0f935" /\ chksum(tla) = "22ecc72f")
VARIABLES x, i, pc, lvqid

vars == << x, i, pc, lvqid >>

ProcSet == (3..4) \cup {5}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 3..4 THEN 1..2
                                   ELSE (** _n1 = 5 **) 1..2]

Init == (* Global variables *)
        /\ x = 4
        /\ i = 1
        (* Process sid *)
        /\ lvqid = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 3..4 -> <<"QPL1","QML">>
                                        [] self = 5 -> <<"SPL","SML1">>]

QPL1(self) == /\ pc[self][1]  = "QPL1"
              /\ i' = i + 31
              /\ pc' = [pc EXCEPT ![self][1] = "QPL2"]
              /\ UNCHANGED << x, lvqid >>

QPL2(self) == /\ pc[self][1]  = "QPL2"
              /\ i' = i + 32
              /\ pc' = [pc EXCEPT ![self][1] = "QPL"]
              /\ UNCHANGED << x, lvqid >>

QPL(self) == /\ pc[self][1]  = "QPL"
             /\ i' = i + 4
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << x, lvqid >>

qid1(self) == QPL1(self) \/ QPL2(self) \/ QPL(self)

QML(self) == /\ pc[self][2]  = "QML"
             /\ x' = 1
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]
             /\ UNCHANGED << i, lvqid >>

qid2(self) == QML(self)

qid(self) == qid1(self) \/ qid2(self)

SPL == /\ pc[5][1]  = "SPL"
       /\ x' = lvqid
       /\ pc' = [pc EXCEPT ![5][1] = "Done"]
       /\ UNCHANGED << i, lvqid >>

sid1 == SPL

SML1 == /\ pc[5][2]  = "SML1"
        /\ i' = i + 61
        /\ pc' = [pc EXCEPT ![5][2] = "SML2"]
        /\ UNCHANGED << x, lvqid >>

SML2 == /\ pc[5][2]  = "SML2"
        /\ i' = i + 62
        /\ pc' = [pc EXCEPT ![5][2] = "Done"]
        /\ UNCHANGED << x, lvqid >>

sid2 == SML1 \/ SML2

sid == sid1 \/ sid2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in 3..4: qid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 3..4 : /\ WF_vars((pc[self][1] # "QPL") /\ qid1(self))
                              /\ SF_vars(QPL1(self)) /\ SF_vars(QPL2(self))
        /\ \A self \in 3..4 : WF_vars(qid2(self)) /\ SF_vars(QML(self))
        /\ WF_vars(sid1) /\ SF_vars(SPL)
        /\ WF_vars((pc[5][2] \notin {"SML1", "SML2"}) /\ sid2)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairnessWfC.tla"
}

