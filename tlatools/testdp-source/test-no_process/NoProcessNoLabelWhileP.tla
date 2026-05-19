------------------------ MODULE NoProcessNoLabelWhileP -------------------------
EXTENDS Naturals, TLC

(*--algorithm Dummy 
variables i = 1;
begin
    while(TRUE) do
        i := i + 1; 
    end while
end algorithm;
*)
=============================================================================
{
    "just-sanity": true,
    "expect-error-check": false,
    "model-checking-args": {},
    "compare_to": "",
    "compare_path": "compile",
    "compare_to": "test-no_process/NoProcessNoLabelWhileC.tla"
}
