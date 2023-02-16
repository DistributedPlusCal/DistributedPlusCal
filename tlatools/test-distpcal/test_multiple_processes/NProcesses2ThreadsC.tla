------------------------ MODULE NProcesses2ThreadsC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
    variables i = 1;
    fair process (pid \in 1..2)
    {
        i := i + 1;
        i := i + 10;
    }
    {
        i := i + 2;
        i := i + 20;
    }

    process(qid \in 3..4)
    {
            i := i + 3;
    }
    {
            i := i + 4;
    }

    fair process(sid = 5)
    {
        i := i + 5;
        i := i + 50;
    }
    {
        i := i + 6;
        i := i + 60;
    }
}

*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsC.tla"
}
