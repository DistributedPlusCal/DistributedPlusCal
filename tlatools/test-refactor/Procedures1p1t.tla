------------------------ MODULE Procedures1p1t -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
\* ASSUME N \in Nat 
\* Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy {
variable c = 0;

procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
				lv := lv + 2;
				x := lv + 3;
        return;
}

process (id = 2)
variable lp = 10, res = 1;
{
   Before:
	      lp := lp + 1;
   Sdr:
        call f(lp);
	 After:
	      res := lp;
} 

}
*)
=============================================================================
