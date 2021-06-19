------------------------ MODULE ReaderWriterC10 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {


fifo chan[Nodes];

macro send_to(i, msg) {
    print(msg);
    print(chan[i]);
		send(chan[i], msg);
}


process ( w \in Nodes )
{
    Read:
      skip;
} {
    Mc:
        send_to(self, "abc");
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-03d0388cde18a25dd874e425bc838057
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Read","Mc">>]

Read(self) == /\ pc[self][1]  = "Read"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]
              /\ chan' = chan

Mc(self) == /\ pc[self][2]  = "Mc"
            /\ PrintT(("abc"))
            /\ PrintT((chan[self]))
            /\ chan' = [chan EXCEPT ![self] =  Append(@, "abc")]
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]

w(self) == Read(self) \/ Mc(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e316a9e766828597a6287ec897b2cbd2


================================================
