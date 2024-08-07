------------------------ MODULE NProcesses2ThreadsSfC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

\* CONSTANT N
N == 2
\* CONSTANT MAXINT
MAXINT == 2

(*--algorithm Dummy {
    variables
		ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
	    x \in 0..MAXINT,               
  	    found = FALSE,
 		i = 1;
		
    fair+ process (pid \in 1..2)
    variables lvpid = 0;
    {
        i := i + 1;
    }
    {
        lvpid := ar[1];
    }

    process(qid \in 3..4)
    {
        PT:+
        i := i + 3;
        PF:
        i := i + 4;
    }
    {
        ar[2] := 1;
    }

    fair process(sid = 5)
    variables lvqid = 1;
    {
        ar[2] := lvqid;
    }
    {
        i := i + 6;
    }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "620daf2a" /\ chksum(tla) = "7c6c8d40")
VARIABLES ar, x, found, i, pc, lvpid, lvqid

vars == << ar, x, found, i, pc, lvpid, lvqid >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [self \in ProcSet |->  CASE self \in 1..2 -> 1..2
                                     []   self \in 3..4 -> 1..2
                                     []   self = 5 -> 1..2 ]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ lvpid = [self \in 1..2 |-> 0]
        (* Process sid *)
        /\ lvqid = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> <<"Lbl_1","Lbl_2">>
                                        [] self \in 3..4 -> <<"PT","Lbl_3">>
                                        [] self = 5 -> <<"Lbl_4","Lbl_5">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ i' = i + 1
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

pid_thread_1(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ lvpid' = [lvpid EXCEPT ![self] = ar[1]]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << ar, x, found, i, lvqid >>

pid_thread_2(self) == Lbl_2(self)

pid(self) == pid_thread_1(self) \/ pid_thread_2(self)

PT(self) == /\ pc[self][1]  = "PT"
            /\ i' = i + 3
            /\ pc' = [pc EXCEPT ![self][1] = "PF"]
            /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

PF(self) == /\ pc[self][1]  = "PF"
            /\ i' = i + 4
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

qid_thread_1(self) == PT(self) \/ PF(self)

Lbl_3(self) == /\ pc[self][2]  = "Lbl_3"
               /\ ar' = [ar EXCEPT ![2] = 1]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << x, found, i, lvpid, lvqid >>

qid_thread_2(self) == Lbl_3(self)

qid(self) == qid_thread_1(self) \/ qid_thread_2(self)

Lbl_4 == /\ pc[5][1]  = "Lbl_4"
         /\ ar' = [ar EXCEPT ![2] = lvqid]
         /\ pc' = [pc EXCEPT ![5][1] = "Done"]
         /\ UNCHANGED << x, found, i, lvpid, lvqid >>

sid_thread_1 == Lbl_4

Lbl_5 == /\ pc[5][2]  = "Lbl_5"
         /\ i' = i + 6
         /\ pc' = [pc EXCEPT ![5][2] = "Done"]
         /\ UNCHANGED << ar, x, found, lvpid, lvqid >>

sid_thread_2 == Lbl_5

sid == sid_thread_1 \/ sid_thread_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in 1..2: pid(self))
           \/ (\E self \in 3..4: qid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : SF_vars(pid_thread_1(self))
        /\ \A self \in 1..2 : SF_vars(pid_thread_2(self))
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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsSfC.tla"
}

