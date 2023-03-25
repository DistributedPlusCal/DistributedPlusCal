------------------------ MODULE NProcesses2ThreadsFairness2ProcIdC -------------------------
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

    procedure g(z)
    variable lvg = 0;
    {
        GPL:+
            lvg := lvg + 31;
        GML:-
			z := lvg + 32;
        return;
    }

    fair process(sid = 5)
    {
        i := i + 4;
        call f(54);
    }
    {
        call g(i);
        call f(i);
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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsFairness2ProcIdC.tla"
}

