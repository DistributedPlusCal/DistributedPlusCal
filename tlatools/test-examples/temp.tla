------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variable c = 0;

procedure f(x) {
    Add:
        c := c + x;
        return;
}

{
    St:
        call f(2);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c0e22c5d063699fa64fce5fa11aad708
CONSTANT defaultInitValue
VARIABLES c, pc, stack, x

vars == << c, pc, stack, x >>

Init == (* Global variables *)
        /\ c = 0
        (* Procedure f *)
        /\ x = defaultInitValue
        /\ stack = << >>
        /\ pc = "St"

Add == /\ pc = "Add"
       /\ c' = c + x
       /\ pc' = Head(stack).pc
       /\ x' = Head(stack).x
       /\ stack' = Tail(stack)

f == Add

St == /\ pc = "St"
      /\ /\ stack' = << [ procedure |->  "f",
                          pc        |->  "Done",
                          x         |->  x ] >>
                      \o stack
         /\ x' = 2
      /\ pc' = "Add"
      /\ c' = c

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == f \/ St
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f0939f89867ca7560be2476514690f18



=========================================================
