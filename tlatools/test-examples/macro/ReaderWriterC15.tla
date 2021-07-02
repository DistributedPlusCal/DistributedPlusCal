------------------------ MODULE ReaderWriterC15 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

fifo chan[Nodes, Nodes];

macro send_to(i, j, msg) {
    send(chan[i, j], msg);
}

process ( w \in Nodes )
{
	Write:
        send_to(self, self, "abc");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-159e2cd22a5a87f6fad498127cabca30
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' = [chan EXCEPT ![self, self] =  Append(@, "abc")]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) == Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0e13c1966b08a33e24e0f5c67371213e


========================================================
