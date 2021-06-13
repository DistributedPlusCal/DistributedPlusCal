------------------------ MODULE Clash -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. 3

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
variable cur = "none";

fifo chan[Nodes];

process ( w \in Nodes )
{
	Write:
    send(chan[self], "msg");
} {
	Read:
  	while ( TRUE ) {
      receive(chan[self], cur);
  	}
} {
  Clear:
		clear(chan);
} {
  Clearness:
		clear(chan);
}
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-924e667ecc5923b521d271942ccb2d1b
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..4]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear","Clearness">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] =  Append(@, "msg")]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ Len(chan[self]) > 0 
              /\ cur' = Head(chan[self])
              /\ chan' = [chan EXCEPT ![self] =  Tail(@) ]
              /\ pc' = [pc EXCEPT ![self][2] = "Read"]

Clear(self) == /\ pc[self][3]  = "Clear"
               /\ chan' = [_n0 \in Nodes |-> <<>>]
               /\ pc' = [pc EXCEPT ![self][3] = "Done"]
               /\ cur' = cur

Clearness(self) == /\ pc[self][4]  = "Clearness"
                   /\ chan' = [_n0 \in Nodes |-> <<>>]
                   /\ pc' = [pc EXCEPT ![self][4] = "Done"]
                   /\ cur' = cur

w(self) == Write(self) \/ Read(self) \/ Clear(self) \/ Clearness(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5486372a166f086a2e1ac21fded743e2
==========================================================

