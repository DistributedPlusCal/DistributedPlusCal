------------------------ MODULE NProcesses2ThreadsNoPcP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy 
    variables i = 1;
    process pid \in 1..2
    begin
        while TRUE do
            i := i + 1;
        end while;
    end process
    begin
        while TRUE do
            i := i + 2;
        end while;
    end subprocess

    process qid \in 3..4
    begin
        while TRUE do
            i := i + 3;
        end while;
    end process
    begin
        while TRUE do
            i := i + 4;
        end while;
    end subprocess

    process sid = 5
    begin
        while TRUE do
            i := i + 5;
        end while;
    end process
    begin
        while TRUE do
            i := i + 6;
        end while;
    end subprocess
end algorithm

*)

=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
		"compare_path": "compile",
    "compare_to": "test_multiple_processes/NProcesses2ThreadsNoPcC.tla"
}
