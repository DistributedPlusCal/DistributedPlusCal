------------------------ MODULE ReaderWriterC14 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variables c = 3;
fifo chan;

macro send_to(x, msg) {
    c := c + x;
    send(chan, msg);
}

process ( w \in Nodes )
{
	Write:
        send_to(2, "abc");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-18913b4587f30b610c107398ff3e8584
VARIABLES c, chan, pc

vars == << c, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [tin29 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ c = 3
        /\ chan = <<>>
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Write(self) == /\ pc[self] [1] = "Write"
               /\ c' = c + 2
               /\ chan' =  Append(chan, "abc")
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]

w(self) ==  \/ Write(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ef791d3e492959934955fe724f1994a6


========================================================
