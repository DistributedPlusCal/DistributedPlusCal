------------------------ MODULE SequentialSendP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm transfer

variable x;
fifo c;

begin
	A: 
    send(c, 2);
    receive(c, x);
    clear(c);
    \* x := Append(c, 1);

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3b6c150494856df3e0e5e64cf0bf1b01
CONSTANT defaultInitValue
VARIABLES x, c, pc

vars == << x, c, pc >>

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ c = <<>>
        /\ pc = "A"

A == /\ pc = "A"
     /\ c' =  Append(c, 2)
     /\ Len(c') > 0 
     /\ x' = Head(c')
     /\ pc' = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ c' =  Tail(c)
         /\ pc' = "Lbl_2"
         /\ x' = x

Lbl_2 == /\ pc = "Lbl_2"
         /\ c' = <<>>
         /\ pc' = "Done"
         /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ca34dff578d6299b59ef526094dc5532

==========================================================
