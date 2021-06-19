------------------------ MODULE logicalClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat Read
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes];

process ( w \in Nodes )
variable cur = 0;
lamportClock clock;
{
    Label1: 
        sendWithClock(chan[self], "msg", clock);
} {
    LC:
        receiveWithClock(chan[self], cur, clock);
} 


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b0940c6fbfb05953cd39d8439844a6db
VARIABLES chan, pc, cur, clock

vars == << chan, pc, cur, clock >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]

(* Comparator for lamport clocks *)
Max(_c, _d) == IF _c > _d THEN _c ELSE _d

Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> 0]
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Label1","LC">>]

Label1(self) == /\ pc[self][1]  = "Label1"
                /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {[msg |-> "msg", clock |-> clock]}]
                /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ cur' = cur

LC(self) == /\ pc[self][2]  = "LC"
            /\ \E _c139 \in chan[self]:
                 /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c139}]
                 /\ clock' = [clock EXCEPT ![self] = Max(clock[self], _c139.clock) + 1]
                 /\ cur' = [cur EXCEPT ![self] = _c139]
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) == Label1(self) \/ LC(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5d4db34463d257b60a65cf3175472799


=========================================================
