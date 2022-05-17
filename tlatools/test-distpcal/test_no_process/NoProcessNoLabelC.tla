------------------------ MODULE NoProcessNoLabelC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables i = 1;
{
        i := i + 1;
}

}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "do_compare": true,
    "compare_to": "test_no_process/NoProcessNoLabelPCAL.tla"
}
