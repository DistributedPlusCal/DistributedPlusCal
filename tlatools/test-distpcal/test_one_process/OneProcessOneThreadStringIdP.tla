------------------------ MODULE OneProcessOneThreadStringIdP -------------------------
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

process pid = "ID"
begin
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
        i := i + 1;
end thread

end algorithm
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 2
    },
    "compare_path": "compile",
    "compare_to": "test_one_process/OneProcessOneThreadStringIdC.tla"
}
