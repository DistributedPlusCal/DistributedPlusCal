------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable x = 0;

process ( w \in Nodes )
lamportClock cl;
{
    Clear:
      reset(cl);
} {
    Inc:
        increase(cl);
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e0ba5a23d1e1d4c9d93e4dec783f68cd
VARIABLES x, pc, cl

vars == << x, pc, cl >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

(* Comparator for Lamport clocks *)
Max(c,d) == IF c > d THEN c ELSE d

Init == (* Global variables *)
        /\ x = 0
        (* Process w *)
        /\ cl = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Clear","Inc">>]

Clear(self) == /\ pc[self] [1] = "Clear"
               /\ cl' = [cl EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ x' = x

Inc(self) == /\ pc[self] [2] = "Inc"
             /\ cl' = [cl EXCEPT ![self] = cl[self] + 1 ]
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]
             /\ x' = x

w(self) ==  \/ Clear(self) \/ Inc(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4c201d6a84dd9554a52a1c07852d8fb3


=========================================================
