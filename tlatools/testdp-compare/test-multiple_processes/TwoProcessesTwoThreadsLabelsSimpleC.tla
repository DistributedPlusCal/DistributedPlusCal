------------------------ MODULE TwoProcessesTwoThreadsLabelsSimpleC  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination ) *)

(*--algorithm Dummy {
variables       
    i = 1;

process ( pid = 1 )
variables n = 0;
{
    a: 
        n := 5;
        \* goto b;
    d: 
        i := n;
}
{
    b:
	    i := 2;
}

process ( qid = 2 )
variables n = 0;
{
    c: 
        n := 5;
        goto d;
    d:
	    i := 2;
}

process ( sid = 3 )
variables n = 0;
{
    c: 
        n := 5;
        goto d;
    d:
	    i := 2;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ad8cd803" /\ chksum(tla) = "777e73f9")
\* Label d of process pid_thread_1 at line 17 col 9 changed to d_
\* Label c of process qid_thread_1 at line 28 col 9 changed to c_
\* Label d of process qid_thread_1 at line 31 col 13 changed to d_q
\* Process variable n of process pid#pid_thread_1##pid_thread_2# at line 11 col 11 changed to n_
\* Process variable n of process qid#qid_thread_1# at line 25 col 11 changed to n_q
VARIABLES pc, i, n_, n_q, n

vars == << pc, i, n_, n_q, n >>

ProcSet == {1} \cup {2} \cup {3}

SubProcSet == [self \in ProcSet |->  CASE self = 1 -> 1..2
                                     []   self = 2 -> 1..1
                                     []   self = 3 -> 1..1 ]

Init == (* Global variables *)
        /\ i = 1
        (* Process pid *)
        /\ n_ = 0
        (* Process qid *)
        /\ n_q = 0
        (* Process sid *)
        /\ n = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> <<"a","b">>
                                        [] self = 2 -> <<"c">>
                                        [] self = 3 -> <<"c">>]

a == /\ pc[1][1]  = "a"
     /\ n_' = 5
     /\ pc' = [pc EXCEPT ![1][1] = "d_"]
     /\ UNCHANGED << i, n_q, n >>

d_ == /\ pc[1][1]  = "d_"
      /\ i' = n_
      /\ pc' = [pc EXCEPT ![1][1] = "Done"]
      /\ UNCHANGED << n_, n_q, n >>

pid_thread_1 == a \/ d_

b == /\ pc[1][2]  = "b"
     /\ i' = 2
     /\ pc' = [pc EXCEPT ![1][2] = "Done"]
     /\ UNCHANGED << n_, n_q, n >>

pid_thread_2 == b

pid == pid_thread_1 \/ pid_thread_2

c_ == /\ pc[2][1]  = "c_"
      /\ n_q' = 5
      /\ pc' = [pc EXCEPT ![2][1] = "d_q"]
      /\ UNCHANGED << i, n_, n >>

d_q == /\ pc[2][1]  = "d_q"
       /\ i' = 2
       /\ pc' = [pc EXCEPT ![2][1] = "Done"]
       /\ UNCHANGED << n_, n_q, n >>

qid_thread_1 == c_ \/ d_q

qid == qid_thread_1

c == /\ pc[3][1]  = "c"
     /\ n' = 5
     /\ pc' = [pc EXCEPT ![3][1] = "d"]
     /\ UNCHANGED << i, n_, n_q >>

d == /\ pc[3][1]  = "d"
     /\ i' = 2
     /\ pc' = [pc EXCEPT ![3][1] = "Done"]
     /\ UNCHANGED << n_, n_q, n >>

sid_thread_1 == c \/ d

sid == sid_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid \/ qid \/ sid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid_thread_1)
        /\ WF_vars(pid_thread_2)
        /\ WF_vars(qid_thread_1)
        /\ WF_vars(sid_thread_1)

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "compare_to": ""
}
