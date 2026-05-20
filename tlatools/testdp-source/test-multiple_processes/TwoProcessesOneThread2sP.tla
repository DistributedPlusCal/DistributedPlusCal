------------------------ MODULE TwoProcessesOneThread2sP  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
\* CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination ) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..3,               
    found = FALSE,
    i = 1;

process pid1 \in  {"P1", "P2"}
begin
    One:
        found := TRUE;
	Two:
		i := i + 1;
end thread

process pid2 = "P3"
begin
    Three:
		x := ar[1];
	Four:
		ar[i] := 0;
end thread

process pid3 = "P4" 
begin
    Five:
		x := ar[1];
	Six:
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
    "compare_to": "test-multiple_processes/TwoProcessesOneThread2sC.tla"
}
