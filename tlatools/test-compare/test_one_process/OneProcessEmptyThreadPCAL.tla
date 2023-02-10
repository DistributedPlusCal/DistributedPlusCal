------------------------ MODULE OneProcessEmptyThreadP -------------------------
EXTENDS Naturals, TLC 

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid = 1
begin
end process

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c675110e" /\ chksum(tla) = "c1fed77d")
VARIABLE i

vars == << i >>

ProcSet == {1}

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ i = 1

pid == pid1

Next == pid

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "compare",
    "compare_to": "test_one_process/OneProcessEmptyThreadPCAL.tla"
}
