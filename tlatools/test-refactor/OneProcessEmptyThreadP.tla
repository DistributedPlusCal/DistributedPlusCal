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
end process

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a03bd6ac" /\ chksum(tla) = "d892d8e6")
VARIABLE i

vars == << i >>

ProcSet == {1}

Init == (* Global variables *)
        /\ i = 1

Next == pid

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
