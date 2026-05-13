------------------------ MODULE TwoProcessOneThreadLabelC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -label) *)

(*--algorithm Dummy {
variables            
    found = FALSE

process ( a = 1 )
variables c = 3;
{
   a1: c := c+1;
   a: c := c+1;
   a_thread_1: c := c+1;
   b_thread_1: c := c+1;
}

process ( b = 2 )
variables c = 3;
{
   a_thread_1: c := c+1;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "730db244" /\ chksum(tla) = "254261f7")
\* Label a of process a at line 14 col 7 changed to a_
\* Label a_thread_1 of process a at line 15 col 16 changed to a_thread_1_
\* Process variable c of process a at line 11 col 11 changed to c_
VARIABLES pc, found, c_, c

vars == << pc, found, c_, c >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ found = FALSE
        (* Process a *)
        /\ c_ = 3
        (* Process b *)
        /\ c = 3
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "a1"
                                        [] self = 2 -> "a_thread_1"]

a1 == /\ pc[1] = "a1"
      /\ c_' = c_+1
      /\ pc' = [pc EXCEPT ![1] = "a_"]
      /\ UNCHANGED << found, c >>

a_ == /\ pc[1] = "a_"
      /\ c_' = c_+1
      /\ pc' = [pc EXCEPT ![1] = "a_thread_1_"]
      /\ UNCHANGED << found, c >>

a_thread_1_ == /\ pc[1] = "a_thread_1_"
               /\ c_' = c_+1
               /\ pc' = [pc EXCEPT ![1] = "b_thread_1"]
               /\ UNCHANGED << found, c >>

b_thread_1 == /\ pc[1] = "b_thread_1"
              /\ c_' = c_+1
              /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ UNCHANGED << found, c >>

a == a1 \/ a_ \/ a_thread_1_ \/ b_thread_1

a_thread_1 == /\ pc[2] = "a_thread_1"
              /\ c' = c+1
              /\ pc' = [pc EXCEPT ![2] = "Done"]
              /\ UNCHANGED << found, c_ >>

b == a_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)
        /\ WF_vars(b)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "compare_to": ""
}
