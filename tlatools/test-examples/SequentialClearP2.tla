------------------------ MODULE SequentialClearP2 -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

fifo f_chan;

begin
	Clear:
		clear(f_chan);
	Add:
		send(f_chan, 2);
	ClearAgain:
		clear(f_chan);


end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-98f8e550892ee718a4cb9e4235677dcd
VARIABLES f_chan, pc

vars == << f_chan, pc >>

Init == (* Global variables *)
        /\ f_chan = <<>>
        /\ pc = "Clear"

Clear == /\ pc = "Clear"
         /\ f_chan' = <<>>
         /\ pc' = "Add"

Add == /\ pc = "Add"
       /\ f_chan' =  Append(f_chan, 2)
       /\ pc' = "ClearAgain"

ClearAgain == /\ pc = "ClearAgain"
              /\ f_chan' = <<>>
              /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Clear \/ Add \/ ClearAgain
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-de0ce96ca77641cc7fefebf71565d50b

===========================================================
