------------------------ MODULE OneProcessOneThreadLVandLabelsP -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)
CONSTANT PROCSet     (* Set of process indexes *)

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process pid \in PROCSet
variables c = 3;
begin
    One:
        found := TRUE;
				x := ar[1];
				c := c+1;
	  Two:
				i := i + 1;
				ar[i] := 0;
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
        "MAXINT": 2,
        "PROCSet": "1..2"
    }
}
