------------------------ MODULE ReaderWriterC6 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

channel chan[Nodes, Nodes];

process ( w \in Nodes )
variable cur = "none", count = 0;
{
	Write:
        send(chan[self, self], "msg");
        count := count + 1;
} {
	Read:
  	while ( TRUE ) {
    	 receive(chan[self, self], cur);
    	 count := count + 1;
  	}
} {
	Clear:
	await ( count = 5 );
	clear(chan);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b6dba7d5bcdba5442286b37f6e86080a
VARIABLES chan, pc, cur, count

vars == << chan, pc, cur, count >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes, _n441 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ count = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self, self] = chan[self, self] \cup {"msg"}]
               /\ count' = [count EXCEPT ![self] = count[self] + 1]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ \E _c139 \in chan[self, self]:
                   /\ chan' = [chan EXCEPT ![self, self] = chan[self, self] \ {_c139}]
                   /\ cur' = [cur EXCEPT ![self] = _c139]
              /\ count' = [count EXCEPT ![self] = count[self] + 1]
              /\ pc' = [pc EXCEPT ![self][2] = "Read"]

Clear(self) == /\ pc[self][3]  = "Clear"
               /\ ( count[self] = 5 )
               /\ chan' = [_n0, _n1 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][3] = "Done"]
               /\ UNCHANGED << cur, count >>

w(self) == Write(self) \/ Read(self) \/ Clear(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e3e24394277882114903aabcacb10f12

==========================================================
