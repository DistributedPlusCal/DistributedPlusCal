------------------------ MODULE ProceduresWithLVprocId -------------------------
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

process (id = 3)
variable r = 1, rr = 2, ar \in [ 1..N -> 0..MAXINT ];
{
   Sdr2:
        call f(37);
}


}
*)
=============================================================================
