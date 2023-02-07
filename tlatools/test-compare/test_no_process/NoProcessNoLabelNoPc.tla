------------------------ MODULE NoProcessNoLabelNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables i = 1;
{
    while(TRUE) {
        i := i + 1;
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3c8834d3" /\ chksum(tla) = "9295e71f")
VARIABLE i

vars == << i >>

Init == (* Global variables *)
        /\ i = 1

Next == i' = i + 1

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "model-checking-args": {},
}
