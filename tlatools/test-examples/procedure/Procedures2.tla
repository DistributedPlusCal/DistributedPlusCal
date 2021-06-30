------------------------ MODULE Procedures2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variable c = 0;

procedure f(x) {
    Send:
        x := x + 2;
        return;
}


{
    Sdr:
        call f(c);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ec3fd10b2bc2b4fcdcd9a5ada2cd7477
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x

vars == << c, pc, stack, x >>

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = defaultInitValue
        /\ stack = << >>
        /\ pc = "Sdr"

Send == /\ pc = "Send"
        /\ x' = x + 2
        /\ pc' = "Lbl_1"
        /\ UNCHANGED << c, stack >>

Lbl_1 == /\ pc = "Lbl_1"
         /\ pc' = Head(stack).pc
         /\ x' = Head(stack).x
         /\ stack' = Tail(stack)
         /\ c' = c

f == Send \/ Lbl_1

Sdr == /\ pc = "Sdr"
       /\ /\ stack' = << [ procedure |->  "f",
                           pc        |->  "Done",
                           x         |->  x ] >>
                       \o stack
          /\ x' = c
       /\ pc' = "Send"
       /\ c' = c

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == f \/ Sdr
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-630fa74c90d6b0a83e91e716e1d2e7c4


=========================================================
