------------------------ MODULE ThreadsC -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-distpcal) *)

(*--algorithm MyAlgo {
    variables
        tab = [ x \in 1..2 |-> 0 ];
    
    process (pid = 3)
    variables lv = 0;
    {
s1: lv := lv + 1;
    tab[1] := tab[1] + lv;
    }
    {
s2: lv := lv + 1;
    tab[2] := tab[2] + lv;
    }

    process (qid \in 1..2)
    variables t = 0;
    {
rc: await tab[self] > 0;
    t := tab[self];
ut: t := t + 1;
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "56412fb2" /\ chksum(tla) = "30c03ea5")
VARIABLES tab, pc, lv, t

vars == << tab, pc, lv, t >>

ProcSet == {3} \cup (1..2)

SubProcSet == [self \in ProcSet |->  CASE self = 3 -> 1..2
                                     []   self \in 1..2 -> 1..1 ]

Init == (* Global variables *)
        /\ tab = [ x \in 1..2 |-> 0 ]
        (* Process pid *)
        /\ lv = 0
        (* Process qid *)
        /\ t = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 3 -> <<"s1","s2">>
                                        [] self \in 1..2 -> <<"rc">>]

s1 == /\ pc[3][1]  = "s1"
      /\ lv' = lv + 1
      /\ tab' = [tab EXCEPT ![1] = tab[1] + lv']
      /\ pc' = [pc EXCEPT ![3][1] = "Done"]
      /\ t' = t

pid_thread_1 == s1

s2 == /\ pc[3][2]  = "s2"
      /\ lv' = lv + 1
      /\ tab' = [tab EXCEPT ![2] = tab[2] + lv']
      /\ pc' = [pc EXCEPT ![3][2] = "Done"]
      /\ t' = t

pid_thread_2 == s2

pid == pid_thread_1 \/ pid_thread_2

rc(self) == /\ pc[self][1]  = "rc"
            /\ tab[self] > 0
            /\ t' = [t EXCEPT ![self] = tab[self]]
            /\ pc' = [pc EXCEPT ![self][1] = "ut"]
            /\ UNCHANGED << tab, lv >>

ut(self) == /\ pc[self][1]  = "ut"
            /\ t' = [t EXCEPT ![self] = t[self] + 1]
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ UNCHANGED << tab, lv >>

qid_thread_1(self) == rc(self) \/ ut(self)

qid(self) == qid_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ (\E self \in 1..2: qid(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
