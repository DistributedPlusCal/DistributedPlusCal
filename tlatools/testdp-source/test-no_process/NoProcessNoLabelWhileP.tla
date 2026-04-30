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
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
    "compare_to": "",
    "compare_path": "compile",
    "compare_to": "test-no_process/NoProcessNoLabelWhileC.tla"
}
