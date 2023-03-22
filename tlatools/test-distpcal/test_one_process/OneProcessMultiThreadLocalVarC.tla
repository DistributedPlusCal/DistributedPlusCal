------------------------ MODULE OneProcessMultiThreadLocalVarC  -------------------------
EXTENDS Naturals, TLC

\* CONSTANT N           (* Size of arrays *)
N == 4
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 4

(* PlusCal options (-termination -label -distpcal) *)

(*--algorithm Dummy {
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    i = 1;

process ( pid = 1 )
variable c = 1;
{
    c := c+1;
    x := ar[c];
}
{
    ar[i] := c;
}

}
*)

=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 4,
        "MAXINT": 4
    }
}
