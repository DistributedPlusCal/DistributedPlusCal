------------------------ MODULE TwoProcessesOneThread2C  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
\* CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in 2..3 )
{
    One:
        found := TRUE;
	  Two:
				i := i + 1;
}

process ( pid2 = 1 )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "80f2f6f1" /\ chksum(tla) = "4bbab297")
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == (2..3) \cup {1}

SubProcSet == [self \in ProcSet |->  CASE self \in 2..3 -> 1..1
                                     []   self = 1 -> 1..1 ]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in 2..3 -> <<"One">>
                                        [] self = 1 -> <<"Three">>]

One(self) == /\ pc[self][1]  = "One"
             /\ found' = TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, x, i >>

Two(self) == /\ pc[self][1]  = "Two"
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << ar, x, found >>

pid1_thread_1(self) == One(self) \/ Two(self)

pid1(self) == pid1_thread_1(self)

Three == /\ pc[1][1]  = "Three"
         /\ x' = ar[1]
         /\ pc' = [pc EXCEPT ![1][1] = "Four"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc[1][1]  = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![1][1] = "Done"]
        /\ UNCHANGED << x, found, i >>

pid2_thread_1 == Three \/ Four

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
    "model-checking-args": {
		    "N": 2,
		    "MAXINT": 2
	},
    "compare_to": "test_multiple_processes/TwoProcessesOneThread2C.tla"
}
