------------------------ MODULE TwoProcessesTwoThreadsLabelsP  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination) *)

(*--algorithm Dummy 
variables       
    i = 1;

process pid1 = 2
variables n = 0;
begin
    a: 
        n := 5;
        i := 1;
        goto b;
    b:
	    i := 2;
end thread
begin
    c: 
        i := 3;
    d: 
        i := 4;
        goto e;
    e: 
        i := 5
end thread

process pid2 \in {1,3}
variables n = 0;
begin
    f: 
        n := 5;
        i := 1;
        goto f;
    g:
	    i := 2;
end thread

end algorithm
*)

=============================================================================
{
	"compare_path": "compile",
    "compare_to": "test-multiple_processes/TwoProcessesTwoThreadsLabelsC.tla"
}
