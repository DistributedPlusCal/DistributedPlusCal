------------------------ MODULE ReaderWriterC17 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan;

macro readFromChannel(x) {
    counter := counter + x;
    receive(chan, cur);
}

process ( w \in Nodes )
variable cur = "none", counter = 0;
{
	Read:
        readFromChannel(2);
} 

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4a4f03d2c36b9e90746285656e9cb6de
VARIABLES chan, pc, cur, counter

vars == << chan, pc, cur, counter >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = <<>>
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ counter = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Read(self) == /\ pc[self][1]  = "Read"
              /\ counter' = [counter EXCEPT ![self] = counter[self] + 2]
              /\ Len(chan) > 0 
              /\ cur' = [cur EXCEPT ![self] = Head(chan)]
              /\ chan' =  Tail(chan)
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e0b61bff87db5ea6d6ab71a5155a59fa


========================================================
