------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..3

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

process (c \in Nodes)
{
    Start:
        send(chan, "msg");
    Rec:
        clear(chan);
}

process (p = 78)
variable  q = 0;
lamportClock clock;
{
    Lab:
        q := q + 1;
        skip;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3650b4f95975a3b9f6663806e5e086b3
VARIABLES chan, pc, q, clock

vars == << chan, pc, q, clock >>

ProcSet == (Nodes) \cup {78}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..1
                                   ELSE (**78**) 1..1]

Init == (* Global variables *)
        /\ chan = [_mn430 \in Nodes |-> {}]
        (* Process p *)
        /\ q = 0
        /\ clock = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Start">>
                                        [] self = 78 -> <<"Lab">>]

Start(self) == /\ pc[self][1]  = "Start"
               /\ chan' = (chan \cup {"msg"})
               /\ pc' = [pc EXCEPT ![self][1] = "Rec"]
               /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
               /\ UNCHANGED << q >>

Rec(self) == /\ pc[self][1]  = "Rec"
             /\ chan' = [_n0 \in Nodes |-> {}]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ UNCHANGED << q >>

c(self) == Start(self) \/ Rec(self)

Lab == /\ pc[78][1]  = "Lab"
       /\ q' = q + 1
       /\ TRUE
       /\ pc' = [pc EXCEPT ![78][1] = "Done"]
       /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
       /\ UNCHANGED << chan >>

p == Lab

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == p
           \/ (\E self \in Nodes: c(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-aadd6a89fd9a474e01edb4956b0c8a93



=========================================================
