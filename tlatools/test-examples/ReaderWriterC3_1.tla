------------------------ MODULE ReaderWriterC3_1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {


channel chan[Nodes];

process ( w \in Nodes )
variable cur = "none";
{
    Write:
          while ( TRUE ) 
          {
        	send(chan[self], "msg");
          };
    Read:
          while ( TRUE ) {
            receive(chan[self], cur);
          }
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-92cd1fb3e58ca87699305e23e8729589
VARIABLES chan, pc, cur

vars == << chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [_dm_23 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = [n0 \in Nodes |-> {}]
        (* Node w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self] [1] = "Read"
              /\ \E c149 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {c149}]
                   /\ cur' = [cur EXCEPT ![self] = c149]
              /\ pc' = [pc EXCEPT ![self][1] = "Read"]

w(self) ==  \/ Write(self) \/ Read(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a98979ecf5648619ae72c445f1f2c4bc

===========================================================
