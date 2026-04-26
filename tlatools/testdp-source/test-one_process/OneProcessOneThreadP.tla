------------------------ MODULE OneProcessOneThreadP -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process pid = 1
variables c = 3;
begin
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
				c := c+1;
end thread

end algorithm;
*)
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 2
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessOneThreadC.tla"
}
