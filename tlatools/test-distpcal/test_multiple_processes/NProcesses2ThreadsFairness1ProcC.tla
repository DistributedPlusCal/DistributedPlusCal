------------------------ MODULE NProcesses2ThreadsFairness1ProcC -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-label -distpcal) *)

PROCSet == 1..2

(*--algorithm Dummy {
    variables
	    x = 4,
 		i = 1;
	
    procedure f(y)
    variable lvf = 0;
    {
        FPL1:+
            lvf := lvf + 11;
        FPL2:+
            lvf := lvf + 12;
        FML1:-
			y := lvf + 21;
        FML2:-
			y := lvf + 22;
        return;
    }

    fair process(qid \in 3..4)
    {
        i := i + 4;
    }
    {
        call f(i);
    }

    fair+ process(sid = 5)
    variables lvqid = 1;
    {
        x := lvqid;
    }
    {
        i := i + 6;
        call f(23);
    }
}

*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
        "defaultInitValue": 0
    },
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairness1ProcC.tla"
}

