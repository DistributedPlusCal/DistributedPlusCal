------------------------ MODULE OneProcessOneThreadLVandLabelsC -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination ) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid \in PROCSet )
variables c = 3;
{
    One:
        found := TRUE;
		x := ar[1];
		c := c+1;
	Two:
		i := i + 1;
		ar[i] := 0;
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fd29a16d" /\ chksum(tla) = "1ecdefbd")
VARIABLES pc, ar, x, found, i, c

vars == << pc, ar, x, found, i, c >>

ProcSet == (PROCSet)

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ found = FALSE
        /\ i = 1
        (* Process pid *)
        /\ c = [self \in PROCSet |-> 3]
        /\ pc = [self \in ProcSet |-> <<"One">>]

One(self) == /\ pc[self][1]  = "One"
             /\ found' = TRUE
             /\ x' = ar[1]
             /\ c' = [c EXCEPT ![self] = c[self]+1]
             /\ pc' = [pc EXCEPT ![self][1] = "Two"]
             /\ UNCHANGED << ar, i >>

Two(self) == /\ pc[self][1]  = "Two"
             /\ i' = i + 1
             /\ ar' = [ar EXCEPT ![i'] = 0]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << x, found, c >>

pid_thread_1(self) == One(self) \/ Two(self)

pid(self) == pid_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCSet: pid(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCSet : WF_vars(pid_thread_1(self))

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 2,
        "PROCSet": "1..2"
    },
    "compare_to": ""
}
