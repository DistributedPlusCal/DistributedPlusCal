------------------------ MODULE OneProcessOneThreadC -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -label -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid = 1 )
variables c = 3;
{
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
				c := c+1;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "976beff7" /\ chksum(tla) = "e3504743")
VARIABLES pc, ar, x, found, i, c

vars == << pc, ar, x, found, i, c >>

ProcSet == {1}

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = 3
        /\ pc = [self \in ProcSet |-> <<"Lbl_1">>]

Lbl_1 == /\ pc[1][1]  = "Lbl_1"
         /\ found' = TRUE
         /\ x' = ar[1]
         /\ i' = i + 1
         /\ ar' = [ar EXCEPT ![i'] = 0]
         /\ c' = c+1
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

pid_thread_1 == Lbl_1

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
    },
    "compare_to": ""
}
