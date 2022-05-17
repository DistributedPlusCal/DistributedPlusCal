------------------------ MODULE OneProcessEmptyThreadPCAL -------------------------
EXTENDS Naturals, TLC 

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Dummy 
variables 
    i = 1;

process pid = 1
begin
end process

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2b0149d4" /\ chksum(tla) = "a7ea8cfc")
VARIABLE i

vars == << i >>

ProcSet == {1}

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ i = 1

Next == pid

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid)

\* END TRANSLATION 
=============================================================================
