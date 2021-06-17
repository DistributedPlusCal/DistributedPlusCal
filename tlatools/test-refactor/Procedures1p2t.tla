------------------------ MODULE Procedures1p2t -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT Nodes     (* Set of process indexes *)
Nodes == 1 .. N
 
(*
--algorithm LamportMutex {
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

process (id = N+1)
variable lp = 10, res = 1;
{
   Before:
	      lp := lp + 1;
   Sdr:
        call f(lp);
	 After:
	      res := lp;
} 

process (idm \in Nodes)
variable lpS = 10, resS = 1;
{
   BeforeS:
	      lpS := lpS + 1;
   SdrS:
        call f(lpS);
	 AfterS:
	      resS := lpS;
} 

} 
*)
=============================================================================
