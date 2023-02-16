------------------------ MODULE NProcesses2ThreadsP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy 
    variables i = 1;
    fair process pid \in 1..2
    begin
        i := i + 1;
        i := i + 10;
    end process
    begin
        i := i + 2;
        i := i + 20;
    end subprocess

    process qid \in 3..4
    begin
            i := i + 3;
    end process
    begin
            i := i + 4;
    end subprocess

    fair process sid = 5
    begin
        i := i + 5;
        i := i + 50;
    end process
    begin
        i := i + 6;
        i := i + 60;
    end subprocess
end algorithm

*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
		"compare_path": "compile",
    "compare_to": "test_multiple_processes/NProcesses2ThreadsC.tla"
}
