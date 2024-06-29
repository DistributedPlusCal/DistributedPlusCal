------------------------ MODULE NProcesses2ThreadsC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

\* CONSTANT N           
N == 2
\* CONSTANT MAXINT      
MAXINT == 2
\* CONSTANT 
PROCSet1 == 1..2
PROCSet2 == 3..4
PROCid == 5

(*--algorithm Dummy {
    variables
		ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
	    x \in 0..MAXINT,               
  	    found = FALSE,
 		i = 1;
		
    fair process (pid \in PROCSet1)
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

    process(qid \in PROCSet2)
    {
        i := i + 3;
        x := ar[1];
    }
    {
        i := i + 4;
        ar[2] := 1;
    }

    fair process(sid = PROCid)
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
\* BEGIN TRANSLATION (chksum(pcal) = "3950b83b" /\ chksum(tla) = "1fe897fe")
VARIABLES ar, x, found, i, pc, lvpid, lvqid

vars == << ar, x, found, i, pc, lvpid, lvqid >>

ProcSet == (PROCSet1) \cup (PROCSet2) \cup {PROCid}

SubProcSet == [self \in ProcSet |->  CASE self \in PROCSet1 -> 1..2
                                     []   self \in PROCSet2 -> 1..2
                                     []   self = PROCid -> 1..2 ]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ lvpid = [self \in PROCSet1 |-> 0]
        (* Process sid *)
        /\ lvqid = 1
        /\ pc = [self \in ProcSet |-> CASE self \in PROCSet1 -> <<"Lbl_1","Lbl_3">>
                                        [] self \in PROCSet2 -> <<"Lbl_5","Lbl_6">>
                                        [] self = PROCid -> <<"Lbl_7","Lbl_9">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 1
               /\ pc' = [pc EXCEPT ![self][1] = "Lbl_2"]
               /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

Lbl_2(self) == /\ pc[self][1]  = "Lbl_2"
               /\ i' = i + 10
               /\ found' = TRUE
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << ar, x, lvpid, lvqid >>

pid_thread_1(self) == Lbl_1(self) \/ Lbl_2(self)

Lbl_3(self) == /\ pc[self][2]  = "Lbl_3"
               /\ i' = i + 2
               /\ pc' = [pc EXCEPT ![self][2] = "Lbl_4"]
               /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

Lbl_4(self) == /\ pc[self][2]  = "Lbl_4"
               /\ i' = i + 20
               /\ lvpid' = [lvpid EXCEPT ![self] = ar[1]]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << ar, x, found, lvqid >>

pid_thread_2(self) == Lbl_3(self) \/ Lbl_4(self)

pid(self) == pid_thread_1(self) \/ pid_thread_2(self)

Lbl_5(self) == /\ pc[self][1]  = "Lbl_5"
               /\ i' = i + 3
               /\ x' = ar[1]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << ar, found, lvpid, lvqid >>

qid_thread_1(self) == Lbl_5(self)

Lbl_6(self) == /\ pc[self][2]  = "Lbl_6"
               /\ i' = i + 4
               /\ ar' = [ar EXCEPT ![2] = 1]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << x, found, lvpid, lvqid >>

qid_thread_2(self) == Lbl_6(self)

qid(self) == qid_thread_1(self) \/ qid_thread_2(self)

Lbl_7 == /\ pc[PROCid][1]  = "Lbl_7"
         /\ x' = ar[1]
         /\ i' = i + 5
         /\ pc' = [pc EXCEPT ![PROCid][1] = "Lbl_8"]
         /\ UNCHANGED << ar, found, lvpid, lvqid >>

Lbl_8 == /\ pc[PROCid][1]  = "Lbl_8"
         /\ i' = i + 50
         /\ ar' = [ar EXCEPT ![2] = lvqid]
         /\ pc' = [pc EXCEPT ![PROCid][1] = "Done"]
         /\ UNCHANGED << x, found, lvpid, lvqid >>

sid_thread_1 == Lbl_7 \/ Lbl_8

Lbl_9 == /\ pc[PROCid][2]  = "Lbl_9"
         /\ i' = i + 6
         /\ pc' = [pc EXCEPT ![PROCid][2] = "Lbl_10"]
         /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

Lbl_10 == /\ pc[PROCid][2]  = "Lbl_10"
          /\ i' = i + 60
          /\ pc' = [pc EXCEPT ![PROCid][2] = "Done"]
          /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

sid_thread_2 == Lbl_9 \/ Lbl_10

sid == sid_thread_1 \/ sid_thread_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in PROCSet1: pid(self))
           \/ (\E self \in PROCSet2: qid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet1 : WF_vars(pid_thread_1(self))
        /\ \A self \in PROCSet1 : WF_vars(pid_thread_2(self))
        /\ WF_vars(sid_thread_1)
        /\ WF_vars(sid_thread_2)

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

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

