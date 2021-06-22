------------------------ MODULE Procedures0p -------------------------
EXTENDS TLC, Integers, Sequences

\* CONSTANT N
\* ASSUME N \in Nat 
\* Nodes == 1 .. N

(* PlusCal options (-distpcal) *)
 
(*
--algorithm Dummy {
variable c = 0, lp = 10, res = 1;

procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
				lv := lv + 2;
				x := lv + 3;
        return;
}

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
