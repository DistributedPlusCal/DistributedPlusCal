------------------------ MODULE TwoProcessesOneThread2Cvars  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    i = 1;

process ( pid1 \in 2..3 )
variable lp = 10;
{
    One:
        lp := lp + 1;
}

process ( pid2 = 1 )
variable lp = 11;
{
    Three:
        lp := lp + 2;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a5ec8d8e" /\ chksum(tla) = "be8c8169")
\* Process variable lp of process pid1#pid1_thread_1# at line 11 col 10 changed to lp_
VARIABLES pc, i, lp_, lp

vars == << pc, i, lp_, lp >>

ProcSet == (2..3) \cup {1}

SubProcSet == [self \in ProcSet |->  CASE self \in 2..3 -> 1..1
                                     []   self = 1 -> 1..1 ]

Init == (* Global variables *)
        /\ i = 1
        (* Process pid1 *)
        /\ lp_ = [self \in 2..3 |-> 10]
        (* Process pid2 *)
        /\ lp = 11
        /\ pc = [self \in ProcSet |-> CASE self \in 2..3 -> <<"One">>
                                        [] self = 1 -> <<"Three">>]

One(self) == /\ pc[self][1]  = "One"
             /\ lp_' = [lp_ EXCEPT ![self] = lp_[self] + 1]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << i, lp >>

pid1_thread_1(self) == One(self)

pid1(self) == pid1_thread_1(self)

Three == /\ pc[1][1]  = "Three"
         /\ lp' = lp + 2
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]
         /\ UNCHANGED << i, lp_ >>

pid2_thread_1 == Three

pid2 == pid2_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid2
           \/ (\E self \in 2..3: pid1(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 2..3 : WF_vars(pid1_thread_1(self))
        /\ WF_vars(pid2_thread_1)

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "compare_to": ""
}
