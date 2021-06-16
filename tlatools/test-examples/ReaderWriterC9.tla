------------------------ MODULE ReaderWriterC9 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {


channel chan[Nodes];

macro send_to(i, msg) {
    send(chan[i], msg);
}

macro receive_from_channel(x, msg, i) {
    cur := cur + x;
    send_to(i, msg);
}

macro cl() {
    clear(chan);
}

process ( w \in Nodes )
variable cur = 0;
{
    Read:
      receive_from_channel(3, "msg", self);
} {
    cl();
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7eac830743dbd34d7b59d659b7bcfb90
VARIABLES chan, pc, cur

vars == << chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes |-> {}]
        (* Process w *)
        /\ cur = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"Read","Lbl_1">>]

Read(self) == /\ pc[self] [1] = "Read"
              /\ cur' = [cur EXCEPT ![self] = cur[self] + 3]
              /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
              /\ pc' = [pc EXCEPT ![self][1] = "Done"]

Lbl_1(self) == /\ pc[self] [2] = "Lbl_1"
               /\ chan' = [_n0 \in Nodes |-> {}]
               /\ pc' = [pc EXCEPT ![self][2] = "Done"]
               /\ cur' = cur

w(self) ==  \/ Read(self) \/ Lbl_1(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c2520a81d2d0e5109eb0df3e5524c94f



=========================================================