------------------------ MODULE Procedures1 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

\* CONSTANT N           (* Size of arrays *)
N == 2
\* CONSTANT MAXINT      (* Size of arrays *)
MAXINT == 3
\* CONSTANT PROCSet     (* Set of process indexes *)
PROCSet == 1 .. 2
 
(*
--algorithm LamportMutex {
variable c = 0;

procedure f(x) {
    Add:
        x := x + 1;
        return;
}

process (id = 2)
variable y;
{
   y := 1;
   Sdr:
        call f(y);
} 

process (idm \in Nodes)
variable z;
{
   z := 2;
   Sdrm:
        call f(c);
} 

}
*)
=============================================================================
