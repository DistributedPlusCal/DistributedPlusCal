------------------------ MODULE Clash -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. 3

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
         \* _c159 = 159;
         \* _n430 = 42;
\* fifo chan[Nodes];
channel chan[Nodes];

process ( w \in Nodes )
{
	Write:
    send(chan[self], "msg");
} {
	Read:
      receive(chan[self], cur);
} {
  Clear:
		clear(chan);
} {
  Clearness:
		clear(chan);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0e7c74425109ecac4f060a7389ee335b
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..4]


Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_mn430 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear","Clearness">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ \E _c179 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c179}]
                   /\ cur' = _c179
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

Clear(self) == /\ pc[self][3]  = "Clear"
               /\ chan' = [_n0 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][3] = "Done"]
               /\ cur' = cur

Clearness(self) == /\ pc[self][4]  = "Clearness"
                   /\ chan' = [_n0 \in Nodes |-> {}]
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-77025e108d25a192491dfe2e59e71d31
==========================================================
