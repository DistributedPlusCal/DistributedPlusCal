------------------------ MODULE NProcesses2ThreadsNoStutteringP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy 
    variables i = 1;
    process pid \in 1..2
    begin
            i := i + 1;
    end thread
    begin
        while TRUE do
            i := i + 2;
        end while;
    end thread

    process qid \in 3..4
    begin
            i := i + 3;
    end thread
    begin
            i := i + 4;
    end thread

    process sid = 5
    begin
            i := i + 5;
    end thread
    begin
            i := i + 6;
    end thread
end algorithm

*)
=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoStutteringC.tla"
}
