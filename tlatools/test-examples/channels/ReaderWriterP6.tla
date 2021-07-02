------------------------ MODULE ReaderWriterP6 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

channel chan[Nodes];

process w \in Nodes
variable cur = "none", count = 0;
begin
	Write:
      	broadcast(chan, "msg");
end process;
begin
	Read:
    	receive(chan[self], cur);
end subprocess;
begin
	Clear:
	await ( count = 5 );
	clear(chan);
	count := 0;
end subprocess;

end algorithm;
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-d6e0056f683c51b97c99386d9366af74
VARIABLES chan, pc, cur, count

vars == << chan, pc, cur, count >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ count = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [_n0 \in Nodes |-> chan[_n0] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << cur, count >>

Read(self) == /\ pc[self][2]  = "Read"
              /\ \E _c139 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c139}]
                   /\ cur' = [cur EXCEPT ![self] = _c139]
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]
              /\ count' = count

Clear(self) == /\ pc[self][3]  = "Clear"
               /\ ( count[self] = 5 )
               /\ chan' = [_n0 \in Nodes |-> {}]
               /\ count' = [count EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self][3] = "Done"]
               /\ cur' = cur

w(self) == Write(self) \/ Read(self) \/ Clear(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-47f06e792fd244041e80da6813aeea9d

==========================================================
