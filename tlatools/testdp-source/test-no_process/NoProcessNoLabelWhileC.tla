------------------------ MODULE NoProcessNoLabelWhileC -------------------------
EXTENDS Naturals, TLC

(*--algorithm Dummy {
variables i = 1;
{
    while(TRUE) {
        i := i + 1; 
    }
}

}
*)
=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": ""

}
