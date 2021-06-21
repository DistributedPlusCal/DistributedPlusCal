------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat Read
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variables c = 11, w = 2;


process (q \in Nodes)
variables x = 3;
lamportClock clock;
{
    rc:
        c := c + 1;
        w := w + 99;
    dd:
        skip;
} {
    cv:
        c := c + 2;
}

 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-463d419688023fa28f0d8273cd7ff836
VARIABLES c, w, pc, x, clock

vars == << c, w, pc, x, clock >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]

(* Comparator for lamport clocks *)
Max(_c, _d) == IF _c > _d THEN _c ELSE _d

Init == (* Global variables *)
        /\ c = 11
        /\ w = 2
        (* Process q *)
        /\ x = [self \in Nodes |-> 3]
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"rc","cv">>]

rc(self) == /\ pc[self][1]  = "rc"
            /\ c' = c + 1
            /\ w' = w + 99
            /\ pc' = [pc EXCEPT ![self][1] = "dd"]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ UNCHANGED << x >>

dd(self) == /\ pc[self][1]  = "dd"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ UNCHANGED << c, w, x >>

cv(self) == /\ pc[self][2]  = "cv"
            /\ c' = c + 2
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ UNCHANGED << w, x >>

q(self) == rc(self) \/ dd(self) \/ cv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: q(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-86ffc46a9e0b4b151a111b8c0a5b3f77


=========================================================
