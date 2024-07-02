------------------------ MODULE TwoProcessesOneThread2Cvars  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination -distpcal) *)

(*--algorithm Dummy {
variables 
    i = 1;

process ( pid1 \in 2..3 )
variable lp = 10;
{
    One:
        lp := lp + 1;
}

process ( pid2 = 1 )
variable lp = 11;
{
    Three:
        lp := lp + 2;
}

}
*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false
}
