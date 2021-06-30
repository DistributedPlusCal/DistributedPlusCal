------------------------ MODULE logicalClock1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat Read
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variables a = 5;
channel chan[Nodes];

process ( w \in Nodes )
lamportClock clock;
{
    Label1: 
        sendWithClock(chan[self], "msg", clock);
    REA:
        a := a + 2;
} {
    LC:
        clear(chan[self]);
} 


process (zz = 98) {
    RD:
        a := a + 1;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9d4903289fb3960cba2887a1977e8f68
VARIABLES a, chan, pc, clock

vars == << a, chan, pc, clock >>

ProcSet == (Nodes) \cup {98}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..2
                                   ELSE (**98**) 1..1]

Init == (* Global variables *)
        /\ a = 5
        /\ chan = [_mn430 \in Nodes |-> {}]
        (* Process w *)
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Label1","LC">>
                                        [] self = 98 -> <<"RD">>]

Label1(self) == /\ pc[self][1]  = "Label1"
                /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {[msg |-> "msg", clock |-> clock]}]
                /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
                /\ pc' = [pc EXCEPT ![self][1] = "REA"]
                /\ a' = a

REA(self) == /\ pc[self][1]  = "REA"
             /\ a' = a + 2
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ UNCHANGED << chan >>

LC(self) == /\ pc[self][2]  = "LC"
            /\ chan' = [chan EXCEPT ![self] = {}]
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ UNCHANGED << a >>

w(self) == Label1(self) \/ REA(self) \/ LC(self)

RD == /\ pc[98][1]  = "RD"
      /\ a' = a + 1
      /\ pc' = [pc EXCEPT ![98][1] = "Done"]
      /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
      /\ UNCHANGED << chan >>

zz == RD

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == zz
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2a9b1cc52e15a892b6f72f0b34df1cf9



=========================================================
