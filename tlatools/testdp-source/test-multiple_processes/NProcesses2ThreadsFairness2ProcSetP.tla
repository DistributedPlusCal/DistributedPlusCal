------------------------ MODULE NProcesses2ThreadsFairness2ProcSetP -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-label ) *)

PROCSet == 1..2

(*--algorithm Dummy 
    variables
	    x = 4,
 		i = 1;
	
    procedure f(y)
    variable lvf = 0;
    begin
        FPL1:+
            lvf := lvf + 11;
        FPL2:+
            lvf := lvf + 12;
        FML1:-
			y := lvf + 21;
        FML2:-
			y := lvf + 22;
        return;
    end procedure

    procedure g(z)
    variable lvg = 0;
    begin
        GPL:+
            lvg := lvg + 31;
        GML:-
			z := lvg + 32;
        return;
    end procedure

    fair process qid \in 3..4
    begin
        i := i + 4;
        call f(54);
    end thread
    begin
        call g(i);
        call f(i);
    end thread

end algorithm

*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
        "defaultInitValue": 0
    },
	"compare_path": "compile",
    "compare_to": "test-multiple_processes/NProcesses2ThreadsFairness2ProcSetC.tla"
}

