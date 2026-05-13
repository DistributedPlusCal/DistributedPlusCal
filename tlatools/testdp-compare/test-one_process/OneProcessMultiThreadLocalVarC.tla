------------------------ MODULE OneProcessMultiThreadLocalVarC  -------------------------
EXTENDS Naturals, TLC

\* CONSTANT N           (* Size of arrays *)
N == 4
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 4

(* PlusCal options (-termination -label -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    i = 1;

process ( pid = 1 )
variable c = 1;
{
    c := c+1;
    x := ar[c];
}
{
    ar[i] := c;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9b030327" /\ chksum(tla) = "ce3ad93a")
VARIABLES pc, ar, x, i, c

vars == << pc, ar, x, i, c >>

ProcSet == {1}

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ i = 1
        (* Process pid *)
        /\ c = 1
        /\ pc = [self \in ProcSet |-> <<"Lbl_1","Lbl_2">>]

Lbl_1 == /\ pc[1][1]  = "Lbl_1"
         /\ c' = c+1
         /\ x' = ar[c']
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]
         /\ UNCHANGED << ar, i >>

pid_thread_1 == Lbl_1

Lbl_2 == /\ pc[1][2]  = "Lbl_2"
         /\ ar' = [ar EXCEPT ![i] = c]
         /\ pc' = [pc EXCEPT ![1][2] = "Done"]
         /\ UNCHANGED << x, i, c >>

pid_thread_2 == Lbl_2

pid == pid_thread_1 \/ pid_thread_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid_thread_1)
        /\ WF_vars(pid_thread_2)

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 

=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 4,
        "MAXINT": 4
    },
    "compare_to": ""
}
