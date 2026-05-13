------------------------ MODULE NoProcessNoLabelNoPcC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-distpcal) *)

(*--algorithm Dummy {
variables i = 1;
{
    while(TRUE) {
        i := i + 1; 
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3c8834d3" /\ chksum(tla) = "abf91524")
VARIABLE i

vars == << i >>

Init == (* Global variables *)
        /\ i = 1

Next == i' = i + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "test_no_process/NoProcessNoLabelNoPc.tla"

}
