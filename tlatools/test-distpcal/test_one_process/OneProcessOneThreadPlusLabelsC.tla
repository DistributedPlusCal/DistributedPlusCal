------------------------ MODULE OneProcessOneThreadPlusLabelsC -------------------------
EXTENDS Naturals, TLC

PROCSet == 1..2

(* PlusCal options (-distpcal) *)

(*--algorithm Dummy {
variables 
    found = FALSE,
    i = 1;

fair process ( pid \in PROCSet )
variables c = 3;
{
    L1:+
        found := TRUE;
    L2:-
        i := i + 1;
}

}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}
