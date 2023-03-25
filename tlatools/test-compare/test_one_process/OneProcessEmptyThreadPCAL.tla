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
\* BEGIN TRANSLATION (chksum(pcal) = "b9dc3160" /\ chksum(tla) = "3cde1cee")
VARIABLE i

vars == << i >>

ProcSet == {1}

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ i = 1

pid == pid1

Next == pid

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid1)

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
