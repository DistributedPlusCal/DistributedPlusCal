------------------------ MODULE OneProcessEmptyThreadP -------------------------
EXTENDS Naturals, TLC 

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid = 1
begin
end thread

end algorithm;
*)

=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": true,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_to": ""
}
