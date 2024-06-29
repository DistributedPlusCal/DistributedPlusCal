------------------------ MODULE TwoProcessOneThreadLabelC -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -label -distpcal) *)

(*--algorithm Dummy {
variables            
    found = FALSE

process ( a = 1 )
variables c = 3;
{
   a1: c := c+1;
   a: c := c+1;
   a_thread_1: c := c+1;
   b_thread_1: c := c+1;
}

process ( b = 2 )
variables c = 3;
{
   a_thread_1: c := c+1;
}

}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"]
}
