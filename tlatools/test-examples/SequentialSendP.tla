------------------------ MODULE SequentialSendP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm transfer

\* variable c = <<>>, x;
fifo c;

begin
	A: 
    send(c, 2);
    \* x := Append(c, 1);

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0357f54b10b0617b81099d20e32f0268
VARIABLES c, pc

vars == << c, pc >>

Init == (* Global variables *)
        /\ c = <<>>
        /\ pc = "A"

A == /\ pc = "A"
     /\ c' =  Append(@, 2)
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-34676f85f1dffe57061c17036d0abb98

==========================================================