------------------------ MODULE NProcesses2ThreadsC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

\* CONSTANT N           
N == 2
\* CONSTANT MAXINT      
MAXINT == 2
\* CONSTANT 
PROCSet1 == 1..2
PROCSet2 == 3..4
PROCid == 5

(*--algorithm Dummy {
    variables
		ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
	    x \in 0..MAXINT,               
  	    found = FALSE,
 		i = 1;
		
    fair process (pid \in PROCSet1)
    variables lvpid = 0;
    {
        i := i + 1;
        i := i + 10;
        found := TRUE;
    }
    {
        i := i + 2;
        i := i + 20;
        lvpid := ar[1];
    }

    process(qid \in PROCSet2)
    {
        i := i + 3;
        x := ar[1];
    }
    {
        i := i + 4;
        ar[2] := 1;
    }

    fair process(sid = PROCid)
    variables lvqid = 1;
    {
        x := ar[1];
        i := i + 5;
        i := i + 50;
        ar[2] := lvqid;
    }
    {
        i := i + 6;
        i := i + 60;
    }
}

*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {
		    "N": 2,
		    "MAXINT": 2
		},
    "compare_to": "test_multiple_processes/NProcesses2ThreadsC.tla"
}

