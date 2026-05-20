------------------------ MODULE TwoProcessesTwoThreadsLabelsSimpleP  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination ) *)

(*--algorithm Dummy
variables       
    i = 1;

process pid = 1
variables n = 0;
begin
    a: 
        n := 5;
        \* goto b;
    d: 
        i := n;
end thread
begin
    b:
	    i := 2;
end thread

process qid = 2
variables n = 0;
begin
    c: 
        n := 5;
        goto d;
    d:
	    i := 2;
end thread

process sid = 3
variables n = 0;
begin
    c: 
        n := 5;
        goto d;
    d:
	    i := 2;
end thread

end algorithm
*)

=============================================================================
{
    "args-check": ["-deadlock"],
	"compare_path": "compile",
    "compare_to": "test-multiple_processes/TwoProcessesTwoThreadsLabelsSimpleC.tla"
}
