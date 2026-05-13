------------------------ MODULE NProcessesNoLabelNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label ) *)

(*--algorithm Dummy {
    variables i = 1;
    process (pid \in 1..2)
    {
        while (TRUE) {
            i := i + 1;
        }
    }

    process(qid \in 3..4)
    {
        while(TRUE) {
            i := i + 3;
        }
    }

    process(sid = 5)
    {
        while(TRUE) {
            i := i + 5;
        }
    }
}

*)

=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": ""
}
