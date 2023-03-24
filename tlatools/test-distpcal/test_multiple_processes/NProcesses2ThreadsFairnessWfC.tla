------------------------ MODULE NProcesses2ThreadsFairnessWfC -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-label -distpcal) *)

PROCSet == 1..2

(*--algorithm Dummy {
    variables
	    x = 4,
 		i = 1;
	
    fair process(qid \in 3..4)
    {
        QPL1:+
            i := i + 31;
        QPL2:+
            i := i + 32;
        QPL:-
            i := i + 4;
    }
    {
        QML:+
            x := 1;
    }

    fair process(sid = 5)
    variables lvqid = 1;
    {
        SPL:+
            x := lvqid;
    }
    {
        SML1:-
            i := i + 61;
        SML2:-
            i := i + 62;
    }
}

*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairnessWfC.tla"
}

