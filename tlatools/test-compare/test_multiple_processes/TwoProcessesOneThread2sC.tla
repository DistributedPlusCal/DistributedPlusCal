------------------------ MODULE TwoProcessesOneThread2sC  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
\* CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..3,               
    found = FALSE,
    i = 1;

process ( pid1 \in  {"P1", "P2"} )
{
    One:
        found := TRUE;
	  Two:
				i := i + 1;
}

process ( pid2 = "P3" )
{
    Three:
				x := ar[1];
	  Four:
				ar[i] := 0;
}

process ( pid3 = "P4" )
{
    Five:
				x := ar[1];
	  Six:
				ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fa14ed18" /\ chksum(tla) = "efa8de")
VARIABLES ar, x, found, i, pc

vars == << ar, x, found, i, pc >>

ProcSet == ({"P1", "P2"}) \cup {"P3"} \cup {"P4"}

SubProcSet == [self \in ProcSet |->  CASE self \in {"P1","P2"} -> 1..1
                                     []   self = "P3" -> 1..1
                                     []   self = "P4" -> 1..1 ]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..3
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> CASE self \in {"P1", "P2"} -> <<"One">>
                                        [] self = "P3" -> <<"Three">>
                                        [] self = "P4" -> <<"Five">>]

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

Three == /\ pc["P3"][1]  = "Three"
         /\ x' = ar[1]
         /\ pc' = [pc EXCEPT !["P3"][1] = "Four"]
         /\ UNCHANGED << ar, found, i >>

Four == /\ pc["P3"][1]  = "Four"
        /\ ar' = [ar EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT !["P3"][1] = "Done"]
        /\ UNCHANGED << x, found, i >>

pid2_thread_1 == Three \/ Four

pid2 == pid2_thread_1

Five == /\ pc["P4"][1]  = "Five"
        /\ x' = ar[1]
        /\ pc' = [pc EXCEPT !["P4"][1] = "Six"]
        /\ UNCHANGED << ar, found, i >>

Six == /\ pc["P4"][1]  = "Six"
       /\ ar' = [ar EXCEPT ![i] = 0]
       /\ pc' = [pc EXCEPT !["P4"][1] = "Done"]
       /\ UNCHANGED << x, found, i >>

pid3_thread_1 == Five \/ Six

pid3 == pid3_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid2 \/ pid3
           \/ (\E self \in {"P1", "P2"}: pid1(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"P1", "P2"} : WF_vars(pid1_thread_1(self))
        /\ WF_vars(pid2_thread_1)
        /\ WF_vars(pid3_thread_1)

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
    "compare_to": "test_multiple_processes/TwoProcessesOneThread2sC.tla"
}
