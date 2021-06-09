------------------------ MODULE OneProcessMultiThread1P  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
CONSTANT MAXINT      (* Size of arrays *)

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    found = FALSE,
    i = 1;


process pid = 1
begin
    Three:
       x := ar[1];
end process;
begin
    Four:
       ar[i] := 0;
end subprocess;

end algorithm;
*)
=============================================================================
