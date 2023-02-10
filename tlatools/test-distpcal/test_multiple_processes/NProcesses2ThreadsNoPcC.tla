------------------------ MODULE NProcesses2ThreadsNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy {
    variables i = 1;
    process (pid \in 1..2)
    {
        while (TRUE) {
            i := i + 1;
        }
    }
    {
        while (TRUE) {
            i := i + 2;
        }
    }

    process(qid \in 3..4)
    {
        while(TRUE) {
            i := i + 3;
        }
    }
    {
        while(TRUE) {
            i := i + 4;
        }
    }

    process(sid = 5)
    {
        while(TRUE) {
            i := i + 5;
        }
    }
    {
        while(TRUE) {
            i := i + 6;
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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoPcC.tla"
}
