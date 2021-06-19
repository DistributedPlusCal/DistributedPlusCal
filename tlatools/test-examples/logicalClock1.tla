------------------------ MODULE logicalClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat Read
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

\* to illustrate auto-adding of clock  increase translations

process ( w \in Nodes )
variable cur = 0, d = 0;
lamportClock clock;
{
    Label1:
        skip;
    Label2:
        cur := 2;
        d := d + 11;
} 


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b19306c07eba83f96b80b479ef639491
VARIABLES pc, cur, d, clock

vars == << pc, cur, d, clock >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]

(* Comparator for lamport clocks *)
Max(c,d) == IF c > d THEN c ELSE d

Init == (* Process w *)
        /\ cur = [self \in Nodes |-> 0]
        /\ d = [self \in Nodes |-> 0]
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Label1">>]

Label1(self) == /\ pc[self][1]  = "Label1"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self][1] = "Label2"]
                /\ UNCHANGED << cur, d, clock >>

Label2(self) == /\ pc[self][1]  = "Label2"
                /\ cur' = [cur EXCEPT ![self] = 2]
                /\ d' = [d EXCEPT ![self] = d[self] + 11]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ clock' = clock

w(self) == Label1(self) \/ Label2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b9ec5fead9847fde198b7db52826582f


=========================================================
