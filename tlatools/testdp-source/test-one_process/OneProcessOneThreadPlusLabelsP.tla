------------------------ MODULE OneProcessOneThreadPlusLabelsP -------------------------
EXTENDS Naturals, TLC

PROCSet == 1..2

(* PlusCal options (-distpcal) *)

(*--algorithm Dummy 
variables 
    found = FALSE,
    i = 1;

fair process pid \in PROCSet
variables c = 3;
begin
    L1:+
        found := TRUE;
    L2:-
        i := i + 1;
end thread

end algorithm;
*)
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessOneThreadPlusLabelsC.tla"
}
