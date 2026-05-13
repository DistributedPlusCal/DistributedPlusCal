------------------------ MODULE OneProcessSetMultiThreadC -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*--algorithm dummy {

variables i = 1;

process ( w \in Nodes )
variables l = 2;
{
	Write:
  	while ( i < 4 ) 
  	{
          i := i+1;
					l := l+2;
  	}
} {
	Read:
  	while ( l < 10 ) {
          i := i+1;
					l := l+2;    	    
  	}
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b04febc3" /\ chksum(tla) = "37eb25d")
VARIABLES pc, i, l

vars == << pc, i, l >>

ProcSet == (Nodes)

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ i = 1
        (* Process w *)
        /\ l = [self \in Nodes |-> 2]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ IF i < 4
                     THEN /\ i' = i+1
                          /\ l' = [l EXCEPT ![self] = l[self]+2]
                          /\ pc' = [pc EXCEPT ![self][1] = "Write"]
                     ELSE /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                          /\ UNCHANGED << i, l >>

w_thread_1(self) == Write(self)

Read(self) == /\ pc[self][2]  = "Read"
              /\ IF l[self] < 10
                    THEN /\ i' = i+1
                         /\ l' = [l EXCEPT ![self] = l[self]+2]
                         /\ pc' = [pc EXCEPT ![self][2] = "Read"]
                    ELSE /\ pc' = [pc EXCEPT ![self][2] = "Done"]
                         /\ UNCHANGED << i, l >>

w_thread_2(self) == Read(self)

w(self) == w_thread_1(self) \/ w_thread_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
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
