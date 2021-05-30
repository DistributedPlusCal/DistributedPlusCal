------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable x = 0;
channel chan[Nodes];

process ( w \in Nodes )
variables cur = "none";
{
    Clear1:
      broadcast(chan, "msg");
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4146bd22d2c85eb0f2b44cf26459a4ed
VARIABLES x, chan, pc, cur

vars == << x, chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1]

(* Comparator for lamport clocks *)
Max(c,d) == IF c > d THEN c ELSE d

Init == (* Global variables *)
        /\ x = 0
        /\ chan = [_n0 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> <<"Clear1">>]

Clear1(self) == /\ pc[self] [1] = "Clear1"
                /\ chan' = [_n0 \in Nodes |-> chan[_n0] \cup {"msg"}]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << x, cur >>

w(self) ==  \/ Clear1(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4738e8b869122b25bb32a9cc4ba752ba


=========================================================
