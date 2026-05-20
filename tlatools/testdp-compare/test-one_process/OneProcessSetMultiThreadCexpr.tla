------------------------ MODULE OneProcessSetMultiThreadCexpr -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. N

(*--algorithm dummy {

variables i = 1;

process ( w \in Nodes \cup {N+1} \cup N+2..N+3)
variables l = 2;
{
	Write:
  	    l := l+2;
} {
	Read:
  	    l := l+4;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "6611fb6b" /\ chksum(tla) = "85d880c5")
VARIABLES pc, i, l

vars == << pc, i, l >>

ProcSet == (Nodes \cup {N+1} \cup N+2..N+3)

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ i = 1
        (* Process w *)
        /\ l = [self \in Nodes \cup {N+1} \cup N+2..N+3 |-> 2]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ l' = [l EXCEPT ![self] = l[self]+2]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ i' = i

w_thread_1(self) == Write(self)

Read(self) == /\ pc[self][2]  = "Read"
              /\ l' = [l EXCEPT ![self] = l[self]+4]
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]
              /\ i' = i

w_thread_2(self) == Read(self)

w(self) == w_thread_1(self) \/ w_thread_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes \cup {N+1} \cup N+2..N+3: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 3
    },
    "compare_to": ""
}
