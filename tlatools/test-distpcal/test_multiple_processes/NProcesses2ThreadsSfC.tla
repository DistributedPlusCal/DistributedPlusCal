------------------------ MODULE NProcesses2ThreadsSfC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -distpcal) *)

\* CONSTANT N
N == 2
\* CONSTANT MAXINT
MAXINT == 2

(*--algorithm Dummy {
    variables
		ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
	    x \in 0..MAXINT,               
  	    found = FALSE,
 		i = 1;
		
    fair+ process (pid \in 1..2)
    variables lvpid = 0;
    {
        i := i + 1;
    }
    {
        lvpid := ar[1];
    }

    process(qid \in 3..4)
    {
        PT:+
        i := i + 3;
        PF:
        i := i + 4;
    }
    {
        ar[2] := 1;
    }

    fair process(sid = 5)
    variables lvqid = 1;
    {
        ar[2] := lvqid;
    }
    {
        i := i + 6;
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
    "compare_to": "test_multiple_processes/NProcesses2ThreadsSfC.tla"
}

