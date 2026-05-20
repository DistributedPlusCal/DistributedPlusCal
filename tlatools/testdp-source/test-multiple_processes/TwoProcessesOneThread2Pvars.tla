------------------------ MODULE TwoProcessesOneThread2Pvars  -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-termination ) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid1 \in 2..3
variable lp = 10;
begin

    One:
        lp := lp + 1;
end thread


process pid2 = 1
variable lp = 11;
begin

    Three:
        lp := lp + 2;
end thread


end algorithm
*)
=============================================================================
{
	"compare_path": "compile",
    "compare_to": "test-multiple_processes/TwoProcessesOneThread2Cvars.tla"
}
