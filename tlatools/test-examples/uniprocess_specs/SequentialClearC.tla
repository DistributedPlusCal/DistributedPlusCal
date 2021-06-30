------------------------ MODULE SequentialClearC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

channel chan;

{
	Clear:
		clear(chan);
	Add:
		send(chan, 2);
	ClearAgain:
		clear(chan);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9d072f8f79f53c566d3526dcd3f29525
VARIABLES chan, pc

vars == << chan, pc >>

Init == (* Global variables *)
        /\ chan = {}
        /\ pc = "Clear"

Clear == /\ pc = "Clear"
         /\ chan' = {}
         /\ pc' = "Add"

Add == /\ pc = "Add"
       /\ chan' = (chan \cup {2})
       /\ pc' = "ClearAgain"

ClearAgain == /\ pc = "ClearAgain"
              /\ chan' = {}
              /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Clear \/ Add \/ ClearAgain
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-953390425935ece0265579c29200dc2d

===========================================
