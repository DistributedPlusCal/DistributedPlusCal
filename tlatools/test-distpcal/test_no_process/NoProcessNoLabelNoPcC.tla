------------------------ MODULE NoProcessNoLabelNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables i = 1;
{
    while(TRUE) {
        i := i + 1;
    }
}

}
*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_no_process/NoProcessNoLabelNoPc.tla"

}
