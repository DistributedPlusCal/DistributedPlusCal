------------------------ MODULE NoProcessNoLabelBasicC -------------------------
EXTENDS Naturals, TLC

(*--algorithm Dummy {
variables i = 1;
{
    i := i + 1;
}

}
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_to": ""
}
