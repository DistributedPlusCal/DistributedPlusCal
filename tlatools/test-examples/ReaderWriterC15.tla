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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b15117aaf21a3ba1f4eba5052f029103
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [n \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = [n0 \in Nodes, n1 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self, self] =  Append(chan[self, self], "abc")]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Write(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-06e7f7a7d3be388ffee2e49965196197


========================================================
