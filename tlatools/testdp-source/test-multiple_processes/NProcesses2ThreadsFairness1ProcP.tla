------------------------ MODULE NProcesses2ThreadsFairness1ProcP -------------------------
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

    fair process qid \in 3..4
    begin
        i := i + 4;
    end thread
    begin
        call f(i);
    end thread

    fair+ process sid = 5
    variables lvqid = 1;
    begin
        x := lvqid;
    end thread
    begin
        i := i + 6;
        call f(23);
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
    "compare_to": "test-multiple_processes/NProcesses2ThreadsFairness1ProcC.tla"
}

