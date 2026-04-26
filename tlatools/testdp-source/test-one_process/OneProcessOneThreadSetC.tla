------------------------ MODULE OneProcessOneThreadSetC -------------------------
EXTENDS Naturals, TLC

MAXINT == 2
N == 3
Nodes == 1 .. N

(* PlusCal options ( -label -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;

process ( pid \in Nodes )
variables c = 3;
{
        found := TRUE;
				x := ar[1];
        i := i + 1;
				ar[i] := 0;
				c := c+1;
}

}
*)
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 2
    }
}
