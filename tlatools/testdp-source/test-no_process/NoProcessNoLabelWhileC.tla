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
    "just-sanity": true,
    "expect-error-check": false,
    "model-checking-args": {},
    "compare_to": ""

}
