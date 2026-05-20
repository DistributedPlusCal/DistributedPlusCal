------------------------ MODULE TwoProcessesOneThread2P  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
\* CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process pid1 \in 2..3 
begin 
    One:
        found := TRUE;
	Two:
	    i := i + 1;
end thread

process pid2 = 1
begin
    Three:
	    x := ar[1];
	Four:
	    ar[i] := 0;
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
    "compare_to": "test-multiple_processes/TwoProcessesOneThread2C.tla"
}
