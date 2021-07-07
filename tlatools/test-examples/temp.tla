------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..3

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

process (l \in Nodes)
lamportClock c;
{
    Start:
        send(chan, "msg");
    Rec:
        clear(chan);
}

process (u = 22)
variable  q = 0;
lamportClock clock;
{
    Lab:
        q := q + 1;
    QAS:
        skip;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c1f1ef370d4fe0a61b3720968c9f738a
VARIABLES chan, pc, c, q, clock

vars == << chan, pc, c, q, clock >>

ProcSet == (Nodes) \cup {22}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..1
                                   ELSE (**22**) 1..1]

Init == (* Global variables *)
        /\ chan = [_mn430 \in Nodes |-> {}]
        (* Process l *)
        /\ c = [self \in Nodes |-> 0]
        (* Process u *)
        /\ q = 0
        /\ clock = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Start">>
                                        [] self = 22 -> <<"Lab">>]

Start(self) == /\ pc[self][1]  = "Start"
               /\ c'  = [c EXCEPT ![self] = c[self] + 1]
               /\ chan' = (chan \cup {"msg"})
               /\ pc' = [pc EXCEPT ![self][1] = "Rec"]
               /\ UNCHANGED << c, q, clock >>

Rec(self) == /\ pc[self][1]  = "Rec"
             /\ c'  = [c EXCEPT ![self] = c[self] + 1]
             /\ chan' = [_n0 \in Nodes |-> {}]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << c, q, clock >>

l(self) == Start(self) \/ Rec(self)

Lab == /\ pc[22][1]  = "Lab"
       /\ clock'  = [clock EXCEPT ![self] = clock[self] + 1]
       /\ q' = q + 1
       /\ pc' = [pc EXCEPT ![22][1] = "QAS"]
       /\ UNCHANGED << chan, c, clock >>

QAS == /\ pc[22][1]  = "QAS"
       /\ clock'  = [clock EXCEPT ![self] = clock[self] + 1]
       /\ TRUE
       /\ pc' = [pc EXCEPT ![22][1] = "Done"]
       /\ UNCHANGED << chan, c, q, clock >>

u == Lab \/ QAS

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == u
           \/ (\E self \in Nodes: l(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5a6cde72e711e4575cd0bc8fadc795b7


=========================================================
