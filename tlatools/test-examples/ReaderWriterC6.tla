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
    	 receive(chan[self], cur);
    	 count := count + 1;
  	}
} {
	Clear:
	await ( count = 5 );
	clear(chan);
	count := 0;
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7beab015a712e3dee5efe5b3db0839d8
VARIABLES chan, pc, cur, count

vars == << chan, pc, cur, count >>

ProcSet == (Nodes)

SubProcSet == [_sub \in ProcSet |-> 1..3]

Init == (* Global variables *)
        /\ chan = [n0 \in Nodes, n1 \in Nodes |-> {}]
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ count = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self, self] = chan[self, self] \cup {"msg"}]
               /\ count' = [count EXCEPT ![self] = count[self] + 1]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self] [2] = "Read"
              /\ \E c139 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {c139}]
                   /\ cur' = [cur EXCEPT ![self] = c139]
              /\ count' = [count EXCEPT ![self] = count[self] + 1]
              /\ pc' = [pc EXCEPT ![self][2] = "Read"]

Clear(self) == /\ pc[self] [3] = "Clear"
               /\ ( count[self] = 5 )
               /\ chan' = [n0 \in Nodes, n1 \in Nodes |-> {}]
               /\ count' = [count EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self][3] = "Done"]
               /\ cur' = cur

w(self) ==  \/ Write(self) \/ Read(self) \/ Clear(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a960dcf4e9e61ef26a7a0b648fc53b0b

==========================================================
