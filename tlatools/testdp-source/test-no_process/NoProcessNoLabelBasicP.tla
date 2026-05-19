------------------------ MODULE NoProcessNoLabelBasicP -------------------------
EXTENDS Naturals, TLC

(*--algorithm Dummy 
variables i = 1;
begin
    i := i + 1;
end algorithm;
*)
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "compile",
    "compare_to": "test-no_process/NoProcessNoLabelBasicC.tla"
}
