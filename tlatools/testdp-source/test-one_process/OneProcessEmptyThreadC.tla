------------------------ MODULE OneProcessEmptyThreadC -------------------------
Extends Naturals, TLC 

(* PlusCal options (-termination  ) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid = 1
{

}

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "73d768d5" /\ chksum(tla) = "292c5098")
VARIABLE i

vars == << i >>

ProcSet == {              1
            {
            
            }}

SubProcSet == [self \in ProcSet |-> 1..0]

Init == (* Global variables *)
        /\ i = 1

pid == 

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "testdp-compare",
    "compare_to": "test-one_process/OneProcessEmptyThreadP.tla"
}
