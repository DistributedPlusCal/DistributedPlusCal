----- MODULE OneProcessOneThreadGotoC----
EXTENDS Naturals, TLC

(* PlusCal options (-termination ) *)

(*--algorithm X {
variables 
    found = FALSE
process (x \in 1..2)
{
    a: goto a;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c22bdb91" /\ chksum(tla) = "6d585083")
VARIABLES pc, found

vars == << pc, found >>

ProcSet == (1..2)

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ found = FALSE
        /\ pc = [self \in ProcSet |-> <<"a">>]

a(self) == /\ pc[self][1]  = "a"
           /\ pc' = [pc EXCEPT ![self][1] = "a"]
           /\ found' = found

x_thread_1(self) == a(self)

x(self) == x_thread_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: x(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(x_thread_1(self))

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "compare_to": ""
}
