------------------------ MODULE ReaderWriterC3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan[Nodes];

process ( w \in Nodes )
variables var;
{
	Write:
                send(chan[self], "msg");
} {
        Read:
                receive(chan[self], var);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-505a7a59efc7493f436074cab2cbb830
CONSTANT defaultInitValue
VARIABLES chan, pc, var

vars == << chan, pc, var >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = [_mn430 \in Nodes |-> <<>>]
        (* Process w *)
        /\ var = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self] =  Append(@, "msg")]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ var' = var

Read(self) == /\ pc[self][2]  = "Read"
              /\ Len(chan[self]) > 0 
              /\ var' = [var EXCEPT ![self] = Head(chan[self])]
              /\ chan' = [chan EXCEPT ![self] =  Tail(@) ]
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) == Write(self) \/ Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-654940ed7bd169dedb26927b0ee25c50

==========================================================
