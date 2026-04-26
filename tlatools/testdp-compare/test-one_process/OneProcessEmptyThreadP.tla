------------------------ MODULE OneProcessEmptyThreadP -------------------------
EXTENDS Naturals, TLC 

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid = 1
begin
end thread

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8a71e5df" /\ chksum(tla) = "1354b145")
VARIABLE i

vars == << i >>

ProcSet == {1}

SubProcSet == [self \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ i = 1

pid == pid_thread_1

Next == pid

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid_thread_1)

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "compare",
    "compare_to": "test-one_process/OneProcessEmptyThreadPCAL.tla"
}
