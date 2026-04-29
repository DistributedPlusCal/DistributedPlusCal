------------------------ MODULE OneProcessOneThreadStringIdC -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid = "ID" )
{
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
        i := i + 1;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "aa0bedb" /\ chksum(tla) = "a074962d")
VARIABLES pc, ar, x, found, i

vars == << pc, ar, x, found, i >>

ProcSet == {"ID"}

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"Lbl_1">>]

Lbl_1 == /\ pc["ID"][1]  = "Lbl_1"
         /\ found' = TRUE
         /\ x' = ar[1]
         /\ i' = i + 1
         /\ ar' = [ar EXCEPT ![i'] = 0]
         /\ pc' = [pc EXCEPT !["ID"][1] = "Lbl_2"]

Lbl_2 == /\ pc["ID"][1]  = "Lbl_2"
         /\ i' = i + 1
         /\ pc' = [pc EXCEPT !["ID"][1] = "Done"]
         /\ UNCHANGED << ar, x, found >>

pid_thread_1 == Lbl_1 \/ Lbl_2

pid == pid_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid_thread_1)

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 2
    }
}
