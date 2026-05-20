------------------------ MODULE NProcesses2ThreadsSfP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label ) *)

\* CONSTANT N
N == 2
\* CONSTANT MAXINT
MAXINT == 2

(*--algorithm Dummy 
    variables
		ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
	    x \in 0..MAXINT,               
  	    found = FALSE,
 		i = 1;
		
    fair+ process pid \in 1..2
    variables lvpid = 0;
    begin
        i := i + 1;
    end thread
    begin
        lvpid := ar[1];
    end thread

    process qid \in 3..4
    begin
        PT:+
        i := i + 3;
        PF:
        i := i + 4;
    end thread
    begin
        ar[2] := 1;
    end thread

    fair process sid = 5 
    variables lvqid = 1;
    begin
        ar[2] := lvqid;
    end thread
    begin
        i := i + 6;
    end thread

end algorithm

*)

=============================================================================
{
    "model-checking-args": {
		    "N": 2,
		    "MAXINT": 2
		},
	"compare_path": "compile",
    "compare_to": "test-multiple_processes/NProcesses2ThreadsSfC.tla"
}

