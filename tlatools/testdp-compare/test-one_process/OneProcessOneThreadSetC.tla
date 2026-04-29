------------------------ MODULE OneProcessOneThreadSetC -------------------------
EXTENDS Naturals, TLC

MAXINT == 2
N == 3
Nodes == 1 .. N

(* PlusCal options ( -label ) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid \in Nodes )
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
\* BEGIN TRANSLATION (chksum(pcal) = "614bab87" /\ chksum(tla) = "50fa622d")
VARIABLES pc, ar, x, found, i, c

vars == << pc, ar, x, found, i, c >>

ProcSet == (Nodes)

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = [self \in Nodes |-> 3]
        /\ pc = [self \in ProcSet |-> <<"Lbl_1">>]

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ found' = TRUE
               /\ x' = ar[1]
               /\ i' = i + 1
               /\ ar' = [ar EXCEPT ![i'] = 0]
               /\ c' = [c EXCEPT ![self] = c[self]+1]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

pid_thread_1(self) == Lbl_1(self)

pid(self) == pid_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: pid(self))
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
        "N": 2,
        "MAXINT": 2
    },
    "compare_to": ""
}
