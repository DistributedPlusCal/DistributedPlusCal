------------------------ MODULE NoProcessNoLabelP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 
variables i = 1;
begin
    i := i + 1;
end algorithm;
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_to": "test_no_process/NoProcessNoLabelPCAL.tla"
}
