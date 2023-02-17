------------------------ MODULE NProcesses2ThreadsC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination -distpcal) *)

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(*--algorithm Dummy {
    variables
		ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
	    x \in 0..MAXINT,               
  	    found = FALSE,
 		i = 1;
		
    fair process (pid \in 1..2)
    variables lvpid = 0;
    {
        i := i + 1;
        i := i + 10;
        found := TRUE;
    }
    {
        i := i + 2;
        i := i + 20;
        lvpid := ar[1];
    }

    process(qid \in 3..4)
    {
        i := i + 3;
        x := ar[1];
    }
    {
        i := i + 4;
        ar[2] := 1;
    }

    fair process(sid = 5)
    variables lvqid = 1;
    {
        x := ar[1];
        i := i + 5;
        i := i + 50;
        ar[2] := lvqid;
    }
    {
        i := i + 6;
        i := i + 60;
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "96719dc7" /\ chksum(tla) = "87a2d0ed")
VARIABLES ar, x, found, i, pc, lvpid, lvqid

vars == << ar, x, found, i, pc, lvpid, lvqid >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 1..2 THEN 1..2
                                 ELSE IF _n1 \in 3..4 THEN 1..2
                                    ELSE (**5**) 1..2]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ lvpid = [self \in 1..2 |-> 0]
        (* Process sid *)
        /\ lvqid = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> <<"Lbl_1","Lbl_3">>
                                        [] self \in 3..4 -> <<"Lbl_5","Lbl_6">>
                                        [] self = 5 -> <<"Lbl_7","Lbl_9">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 1
               /\ pc' = [pc EXCEPT ![self][1] = "Lbl_2"]
               /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

Lbl_2(self) == /\ pc[self][1]  = "Lbl_2"
               /\ i' = i + 10
               /\ found' = TRUE
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << ar, x, lvpid, lvqid >>

pid1(self) == Lbl_1(self) \/ Lbl_2(self)

Lbl_3(self) == /\ pc[self][2]  = "Lbl_3"
               /\ i' = i + 2
               /\ pc' = [pc EXCEPT ![self][2] = "Lbl_4"]
               /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

Lbl_4(self) == /\ pc[self][2]  = "Lbl_4"
               /\ i' = i + 20
               /\ lvpid' = [lvpid EXCEPT ![self] = ar[1]]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << ar, x, found, lvqid >>

pid2(self) == Lbl_3(self) \/ Lbl_4(self)

pid(self) == pid1(self) \/ pid2(self)

Lbl_5(self) == /\ pc[self][1]  = "Lbl_5"
               /\ i' = i + 3
               /\ x' = ar[1]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << ar, found, lvpid, lvqid >>

qid1(self) == Lbl_5(self)

Lbl_6(self) == /\ pc[self][2]  = "Lbl_6"
               /\ i' = i + 4
               /\ ar' = [ar EXCEPT ![2] = 1]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << x, found, lvpid, lvqid >>

qid2(self) == Lbl_6(self)

qid(self) == qid1(self) \/ qid2(self)

Lbl_7 == /\ pc[5][1]  = "Lbl_7"
         /\ x' = ar[1]
         /\ i' = i + 5
         /\ pc' = [pc EXCEPT ![5][1] = "Lbl_8"]
         /\ UNCHANGED << ar, found, lvpid, lvqid >>

Lbl_8 == /\ pc[5][1]  = "Lbl_8"
         /\ i' = i + 50
         /\ ar' = [ar EXCEPT ![2] = lvqid]
         /\ pc' = [pc EXCEPT ![5][1] = "Done"]
         /\ UNCHANGED << x, found, lvpid, lvqid >>

sid1 == Lbl_7 \/ Lbl_8

Lbl_9 == /\ pc[5][2]  = "Lbl_9"
         /\ i' = i + 6
         /\ pc' = [pc EXCEPT ![5][2] = "Lbl_10"]
         /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

Lbl_10 == /\ pc[5][2]  = "Lbl_10"
          /\ i' = i + 60
          /\ pc' = [pc EXCEPT ![5][2] = "Done"]
          /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

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
        /\ \A self \in 3..4 : WF_vars(qid(self))
        /\ WF_vars(sid)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
		    "N": 2,
		    "MAXINT": 2
		},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsC.tla"
}

