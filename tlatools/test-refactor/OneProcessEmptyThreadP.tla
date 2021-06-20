------------------------ MODULE OneProcessEmptyThreadP -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 

variables 
    i = 1;

process pid = 1
begin
end process;

end algorithm;
*)
=============================================================================