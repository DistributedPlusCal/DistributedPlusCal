------------------------ MODULE TwoProcessesTwoThreadsLabelsC  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
variables       
    i = 1;

process ( pid1 = 2 )
variables n = 0;
{
    a: 
        n := 5;
        i := 1;
        goto b;
    b:
	    i := 2;
}
{
    c: 
        i := 3;
    d: 
        i := 4;
        goto e;
    e: 
        i := 5
}

process ( pid2 \in {1,3} )
variables n = 0;
{
    f: 
        n := 5;
        i := 1;
        goto f;
    g:
	    i := 2;
}
}
*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false
}
