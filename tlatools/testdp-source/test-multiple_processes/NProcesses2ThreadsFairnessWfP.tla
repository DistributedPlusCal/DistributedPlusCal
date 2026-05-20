------------------------ MODULE NProcesses2ThreadsFairnessWfP -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-label ) *)

PROCSet == 1..2

(*--algorithm Dummy 
    variables
	    x = 4,
 		i = 1;
	
    fair process qid \in 3..4
    begin
        QPL1:+
            i := i + 31;
        QPL2:+
            i := i + 32;
        QPL:-
            i := i + 4;
    end thread
    begin
        QML:+
            x := 1;
    end thread

    fair process sid = 5
    variables lvqid = 1;
    begin
        SPL:+
            x := lvqid;
    end thread
    begin
        SML1:-
            i := i + 61;
        SML2:-
            i := i + 62;
    end thread

end algorithm
*)

=============================================================================
{
    "model-checking-args": {},
	"compare_path": "compile",
    "compare_to": "test-multiple_processes/NProcesses2ThreadsFairnessWfC.tla"
}

