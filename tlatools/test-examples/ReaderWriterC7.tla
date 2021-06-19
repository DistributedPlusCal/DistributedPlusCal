------------------------ MODULE ReaderWriterC7 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
channel chan[Nodes];

process ( w \in Nodes )
{
	Write:
       	send(chan[self], "msg");
} {
	Read:
    	     receive(chan[self], cur);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-cb561692dcf4a67f31f39d98b5f1f4b5
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n430 \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ \E _c149 \in chan[self]:
                   /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c149}]
                   /\ cur' = _c149
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) == Write(self) \/ Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-914b0a97954a81178daef890088400f0

===============================================================
