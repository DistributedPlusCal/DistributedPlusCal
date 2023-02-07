------------------------ MODULE NProcessesNoLabelNoPcC.tla -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -label -distpcal) *)

(*--algorithm Dummy {
variables i = 1;
    process (pid \in [0..3])
    {
        while(TRUE) {
            i := i + 1;
        }
    }

    process (qid \in [1..2])
    {
        while(TRUE) {
            i := i + 3;
        }
    }
}

*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
}
