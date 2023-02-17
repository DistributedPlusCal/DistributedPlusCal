------------------------ MODULE TwoProcessesTwoThreadsLvC  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
\* CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid1 \in 2..3 )
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
\* BEGIN TRANSLATION (chksum(pcal) = "42ba6100" /\ chksum(tla) = "76bc6feb")
VARIABLES ar, x, found, i, pc, lvpid1, lvpid2

vars == << ar, x, found, i, pc, lvpid1, lvpid2 >>

ProcSet == (2..3) \cup {1}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in 2..3 THEN 1..2
                                 ELSE (**1**) 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid1 *)
        /\ lvpid1 = [self \in 2..3 |-> 0]
        (* Process pid2 *)
        /\ lvpid2 = 10
        /\ pc = [self \in ProcSet |-> CASE self \in 2..3 -> <<"Lbl_1","Lbl_2">>
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
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == pid2
           \/ (\E self \in 2..3: pid1(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 2..3 : WF_vars(pid1(self))
        /\ WF_vars(pid2)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

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
