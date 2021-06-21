------------------------ MODULE ProceduresWithLVprocSet -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
N == 2
MAXINT == 3
\* ASSUME N \in Nat 
\* Nodes == 1 .. 3

(* PlusCal options (-distpcal) *)

(*
--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Add:
				lv := lv + 2;
				r := r + lv;
				rr := rr + r + lv;
				ar[1] := ar[1] + r;
        return;
}

process (pid \in 1..2)
variable r = 2, rr = 1, ar \in [ 1..N -> 0..MAXINT ];
{
   Sdr:
        call f(127);
	 Inc:
	      r := r + 1;
}


}
*)
=============================================================================
