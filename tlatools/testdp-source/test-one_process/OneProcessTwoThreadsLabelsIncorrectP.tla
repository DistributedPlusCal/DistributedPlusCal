------------------------ MODULE OneProcessTwoThreadsLabelsIncorrectP  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy
variables       
    i = 1;

process ( pid1 = 2 )
variables n;
begin
a:      goto b;
end thread;
begin
b:      goto a;
end thread;

end algorithm;
*)

=============================================================================
{
    "expect-error-parse": true,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {  },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessTwoThreadsLabelsIncorrectC.tla"
}
