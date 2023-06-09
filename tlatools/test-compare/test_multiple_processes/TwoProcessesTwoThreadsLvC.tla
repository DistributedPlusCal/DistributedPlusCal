------------------------ MODULE TwoProcessesTwoThreadsLvC  -------------------------
EXTENDS Naturals, TLC

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 2
\* CONSTANT PROCSet     (* Set of process indexes *)
PROCSet == 2..3
(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in PROCSet )
variables lvpid1 = 0;
{
    found := TRUE;
	i := i + 1;
    lvpid1 := i;
}
{
    found := TRUE;
	i := i + 1;
    lvpid1 := i;
}

process ( pid2 = 1 )
variables lvpid2 = 10;
{
	x := ar[1];
	ar[i] := 0;
    lvpid2 := x;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8443dc2c" /\ chksum(tla) = "2a3b607a")
VARIABLES ar, x, found, i, pc, lvpid1, lvpid2

vars == << ar, x, found, i, pc, lvpid1, lvpid2 >>

ProcSet == (PROCSet) \cup {1}

SubProcSet == [self \in ProcSet |->  CASE self \in PROCSet -> 1..2
                                     []   self = 1 -> 1..1 ]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid1 *)
        /\ lvpid1 = [self \in PROCSet |-> 0]
        (* Process pid2 *)
        /\ lvpid2 = 10
        /\ pc = [self \in ProcSet |-> CASE self \in PROCSet -> <<"Lbl_1","Lbl_2">>
                                        [] self = 1 -> <<"Lbl_3">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ found' = TRUE
               /\ i' = i + 1
               /\ lvpid1' = [lvpid1 EXCEPT ![self] = i']
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << ar, x, lvpid2 >>

pid11(self) == Lbl_1(self)

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ found' = TRUE
               /\ i' = i + 1
               /\ lvpid1' = [lvpid1 EXCEPT ![self] = i']
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ UNCHANGED << ar, x, lvpid2 >>

pid12(self) == Lbl_2(self)

pid1(self) == pid11(self) \/ pid12(self)

Lbl_3 == /\ pc[1][1]  = "Lbl_3"
         /\ x' = ar[1]
         /\ ar' = [ar EXCEPT ![i] = 0]
         /\ lvpid2' = x'
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]
         /\ UNCHANGED << found, i, lvpid1 >>

pid21 == Lbl_3

pid2 == pid21

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid2
           \/ (\E self \in PROCSet: pid1(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : WF_vars(pid11(self))
        /\ \A self \in PROCSet : WF_vars(pid12(self))
        /\ WF_vars(pid21)

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
    "compare_to": "test_multiple_processes/TwoProcessesTwoThreadsLvC.tla"
}
