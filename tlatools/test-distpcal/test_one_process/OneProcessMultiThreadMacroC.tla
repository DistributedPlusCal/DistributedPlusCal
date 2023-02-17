------------------------ MODULE OneProcessMultiThreadMacroC  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
\* N == 2
CONSTANT MAXINT      (* Size of arrays *)
\* MAXINT == 3

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    i = 1;

macro mymacro(ind,newv) {
    ar[ind] := newv;
	ind := ind + 1;
}

process ( pid = 1 )
{
    x := 1;
	mymacro(i,x);
}
{
	mymacro(i,x);
    ar[i] := 0;
}

}
*)
 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 3
    }
}
