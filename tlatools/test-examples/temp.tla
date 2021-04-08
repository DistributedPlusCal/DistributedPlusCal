------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

channel chan;

process rm = 1 
begin
	Start:
	send(chan, 2);
end process;


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0665bda886cced199b99c826d1c04b18
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == {1}

SubProcSet == [n \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = {}
        /\ pc = [self \in ProcSet |-> <<"Start">>]

Start == /\ pc[1] [1] = "Start"
         /\ chan' = (chan \cup {2})
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

rm ==  \/ Start

Next == rm

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a4e2b1b923c4036d63c6f7739d1ec7ec


===========================================
