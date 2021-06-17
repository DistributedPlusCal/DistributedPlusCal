------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variable cur = "none";
channel chan[Nodes];
fifo f_chan;

process ( w \in Nodes )
lamportClock clock;
{
    rc:
        receiveWithClock(chan[self], cur, clock);
} {
    sd:
        sendWithClock(chan[self], "msg", clock);
} {
    brd:
        broadcastWithClock(chan, "msg", clock);
}

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a3fd385db98eeae26ce954429fd9cf33
VARIABLES cur, chan, pc, clock

vars == << cur, chan, pc, clock >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]

(* Comparator for lamport clocks *)
Max(c,d) == IF c > d THEN c ELSE d

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"rc","sd","brd">>]

rc(self) == /\ pc[self][1]  = "rc"
            /\ \E _c149 \in chan[self]:
                 /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c149}]
                 /\ clock' = [clock EXCEPT ![self] = Max(clock[self], _c149.clock) + 1]
                 /\ cur' = _c149
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]

sd(self) == /\ pc[self][2]  = "sd"
            /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {[msg |-> "msg", clock |-> clock]}]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]
            /\ cur' = cur

brd(self) == /\ pc[self][3]  = "brd"
             /\ chan' = [_n0 \in Nodes |-> chan[_n0] \cup {[msg |-> "msg", clock |-> clock]}]
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
             /\ pc' = [pc EXCEPT ![self][3] = "Done"]
             /\ cur' = cur

w(self) == rc(self) \/ sd(self) \/ brd(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f21dd23f8d256144a413b0d05d976139


=========================================================
