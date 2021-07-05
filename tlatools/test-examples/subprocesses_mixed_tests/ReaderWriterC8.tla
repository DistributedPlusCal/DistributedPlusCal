------------------------ MODULE ReaderWriterC8 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variables cur = 2;
fifo chan;

macro send1(msg) {
    send(chan, msg);
}

macro read1(x) {
    receive(chan, x);
}

macro clear1() {
    clear(chan);
}

process ( w \in Nodes )
{
	Write:
        send1("msg");
} {
    Read:
        read1(cur);
} {
    Clear:
        clear1();
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7d644e31b3092d7fb8eec99c8e149942
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ cur = 2
        /\ chan = <<>>
        /\ pc = [self \in ProcSet |-> <<"Write","Read","Clear">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ chan' =  Append(chan, "msg")
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ cur' = cur

Read(self) == /\ pc[self][2]  = "Read"
              /\ Len(chan) > 0 
              /\ cur' = Head(chan)
              /\ chan' =  Tail(chan)
              /\ pc' = [pc EXCEPT ![self][2] = "Done"]

Clear(self) == /\ pc[self][3]  = "Clear"
               /\ chan' = <<>>
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3b6ad95785335401457e00b56f70558d


========================================================
