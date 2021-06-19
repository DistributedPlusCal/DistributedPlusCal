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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4d9cc57ccbb7bfb7848f45c910654519
VARIABLES chan, pc, cur

vars == << chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Write"]
               /\ cur' = cur

Read(self) == /\ pc[self][1]  = "Read"
              /\ \E _c149 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c149}]
                   /\ cur' = [cur EXCEPT ![self] = _c149]
              /\ pc' = [pc EXCEPT ![self][1] = "Read"]

w(self) == Write(self) \/ Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f21b29728e4fcd258be0a3aa14597baf

===========================================================
