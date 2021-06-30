------------------------ MODULE SingleProcessSendP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

fifo chan;

process rm = 1 
begin
	Start:
	send(chan, 2);
end process;


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a97299b80feddb06c315f6bc1bb29cf8
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = <<>>
        /\ pc = [self \in ProcSet |-> <<"Start">>]

Start == /\ pc[1][1]  = "Start"
         /\ chan' =  Append(chan, 2)
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

rm == Start

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == rm
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b8350fbd3b20ab2b4cc8b7531dfab8e6


==========================================================
