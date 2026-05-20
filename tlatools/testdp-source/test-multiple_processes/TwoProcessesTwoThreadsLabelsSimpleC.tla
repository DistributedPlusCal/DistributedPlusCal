------------------------ MODULE TwoProcessesTwoThreadsLabelsSimpleC  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination ) *)

(*--algorithm Dummy {
variables       
    i = 1;

process ( pid = 1 )
variables n = 0;
{
    a: 
        n := 5;
        \* goto b;
    d: 
        i := n;
}
{
    b:
	    i := 2;
}

process ( qid = 2 )
variables n = 0;
{
    c: 
        n := 5;
        goto d;
    d:
	    i := 2;
}

process ( sid = 3 )
variables n = 0;
{
    c: 
        n := 5;
        goto d;
    d:
	    i := 2;
}
}
*)

=============================================================================
{
    "args-check": ["-deadlock"],
    "compare_to": ""
}
