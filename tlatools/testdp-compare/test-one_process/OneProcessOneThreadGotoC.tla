----- MODULE OneProcessOneThreadGotoC----

(*--algorithm X {
variables 
    found = FALSE
    process (x \in {})
    {
a:      goto a;
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "807107b7" /\ chksum(tla) = "5bfb6e0")
VARIABLES pc, found

vars == << pc, found >>

ProcSet == ({})

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

Next == (\E self \in {}: x(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"]
}
