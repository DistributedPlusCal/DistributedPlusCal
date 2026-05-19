------------------------ MODULE OneProcessEmptyThreadC -------------------------
Extends Naturals, TLC 

(* PlusCal options (-termination  ) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid = 1
{

}

end algorithm;
*)

=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "testdp-compare",
    "compare_to": "test-one_process/OneProcessEmptyThreadP.tla"
}
