------------------------ MODULE OneProcessMultiThreadMacroP  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
\* N == 2
CONSTANT MAXINT      (* Size of arrays *)
\* MAXINT == 3

(* PlusCal options (-label -termination ) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    i = 1;

macro mymacro(ind,newv)
begin
    ar[ind] := newv;
	ind := ind + 1;
end macro

process pid = 1
begin
    x := 1;
	mymacro(i,x);
end thread
begin
	mymacro(i,x);
    ar[i] := 0;
end thread

end algorithm;
*)

=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 3
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessMultiThreadMacroC.tla"
}
