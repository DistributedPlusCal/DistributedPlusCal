------------------------ MODULE TwoProcessesTwoThreadsLabelsC  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination) *)

(*--algorithm Dummy {
variables       
    i = 1;

process ( pid1 = 2 )
variables n = 0;
{
    a: 
        n := 5;
        i := 1;
        goto b;
    b:
	    i := 2;
}
{
    c: 
        i := 3;
    d: 
        i := 4;
        goto e;
    e: 
        i := 5
}

process ( pid2 \in {1,3} )
variables n = 0;
{
    f: 
        n := 5;
        i := 1;
        goto f;
    g:
	    i := 2;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3060ecb4" /\ chksum(tla) = "891fc450")
\* Process variable n of process pid1#pid1_thread_1##pid1_thread_2# at line 11 col 11 changed to n_
VARIABLES pc, i, n_, n

vars == << pc, i, n_, n >>

ProcSet == {2} \cup ({1,3})

SubProcSet == [self \in ProcSet |->  CASE self = 2 -> 1..2
                                     []   self \in {1,3} -> 1..1 ]

Init == (* Global variables *)
        /\ i = 1
        (* Process pid1 *)
        /\ n_ = 0
        (* Process pid2 *)
        /\ n = [self \in {1,3} |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 2 -> <<"a","c">>
                                        [] self \in {1,3} -> <<"f">>]

a == /\ pc[2][1]  = "a"
     /\ n_' = 5
     /\ i' = 1
     /\ pc' = [pc EXCEPT ![2][1] = "b"]
     /\ n' = n

b == /\ pc[2][1]  = "b"
     /\ i' = 2
     /\ pc' = [pc EXCEPT ![2][1] = "Done"]
     /\ UNCHANGED << n_, n >>

pid1_thread_1 == a \/ b

c == /\ pc[2][2]  = "c"
     /\ i' = 3
     /\ pc' = [pc EXCEPT ![2][2] = "d"]
     /\ UNCHANGED << n_, n >>

d == /\ pc[2][2]  = "d"
     /\ i' = 4
     /\ pc' = [pc EXCEPT ![2][2] = "e"]
     /\ UNCHANGED << n_, n >>

e == /\ pc[2][2]  = "e"
     /\ i' = 5
     /\ pc' = [pc EXCEPT ![2][2] = "Done"]
     /\ UNCHANGED << n_, n >>

pid1_thread_2 == c \/ d \/ e

pid1 == pid1_thread_1 \/ pid1_thread_2

f(self) == /\ pc[self][1]  = "f"
           /\ n' = [n EXCEPT ![self] = 5]
           /\ i' = 1
           /\ pc' = [pc EXCEPT ![self][1] = "f"]
           /\ n_' = n_

g(self) == /\ pc[self][1]  = "g"
           /\ i' = 2
           /\ pc' = [pc EXCEPT ![self][1] = "Done"]
           /\ UNCHANGED << n_, n >>

pid2_thread_1(self) == f(self) \/ g(self)

pid2(self) == pid2_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid1
           \/ (\E self \in {1,3}: pid2(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid1_thread_1)
        /\ WF_vars(pid1_thread_2)
        /\ \A self \in {1,3} : WF_vars(pid2_thread_1(self))

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "compare_to": ""
}
