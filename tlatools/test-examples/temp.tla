------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..3

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

process (c \in Nodes)
lamportClock clock;
{
    L1:
        sendWithClock(chan[self], "msg", clock);
    L2:
        broadcastWithClock(chan, "msg", clock);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-12fd09a7d721e0b0780aa3e5212ed1ac
VARIABLES chan, pc, clock

vars == << chan, pc, clock >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]

(* Comparator for lamport clocks *)
Max(_c, _d) == IF _c > _d THEN _c ELSE _d

Init == (* Global variables *)
        /\ chan = [_mn430 \in Nodes |-> {}]
        (* Process c *)
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"L1">>]

L1(self) == /\ pc[self][1]  = "L1"
            /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {[msg |-> "msg", clock |-> clock]}]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
            /\ pc' = [pc EXCEPT ![self][1] = "L2"]

L2(self) == /\ pc[self][1]  = "L2"
            /\ chan' = [_n0 \in Nodes |-> chan[_n0] \cup {[msg |-> "msg", clock |-> clock]}]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]

c(self) == L1(self) \/ L2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: c(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c4e3b7249e25454a9188ace5688ab429



=========================================================
