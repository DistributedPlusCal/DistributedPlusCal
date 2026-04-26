------------------------ MODULE OneProcessMultiThreadLocalVarP  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    i = 1;

process pid = 1 
variable c = 1;
begin
	c := c+1;
    x := ar[c];
end thread
begin
    ar[i] := c;
end thread

end algorithm;
*)
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 4,
        "MAXINT": 4
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessMultiThreadLocalVarC.tla"
}
