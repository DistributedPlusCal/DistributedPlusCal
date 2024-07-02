------------------------ MODULE OneProcessTwoThreadsLabelsIncorrectC  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy {
variables       
    i = 1;

process ( pid1 = 2 )
variables n;
    {
a:      goto b;
    }
    {
b:      goto a;
    }

}
*)

=============================================================================
{
    "need-error-parse": true,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {  }
}
