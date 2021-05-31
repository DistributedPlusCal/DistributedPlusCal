------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable x = 0;
channel chan;

process ( w \in Nodes )
variables cur = "none";
{
    Clear1:
      clear(chan);
} {
    Send1:
        send(chan, "msg");
    Br1:
        broadcast(chan, "msg");
} {
    Rc1:
        receive(chan, cur);
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c39fafa4abf875b256e09efce84bbac5
VARIABLES x, chan, pc, cur

vars == << x, chan, pc, cur >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..3]


Init == (* Global variables *)
        /\ x = 0
        /\ chan = {}
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> <<"Clear1","Send1","Rc1">>]

Clear1(self) == /\ pc[self] [1] = "Clear1"
                /\ chan' = {}
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << x, cur >>

Send1(self) == /\ pc[self] [2] = "Send1"
               /\ chan' = (chan \cup {"msg"})
               /\ pc' = [pc EXCEPT ![self][2] = "Br1"]
               /\ UNCHANGED << x, cur >>

Br1(self) == /\ pc[self] [2] = "Br1"
             /\ chan' = (chan \cup {"msg"})
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]
             /\ UNCHANGED << x, cur >>

Rc1(self) == /\ pc[self] [3] = "Rc1"
             /\ \E _c149 \in chan:
                  /\ chan' = chan \ {_c149}
                  /\ cur' = [cur EXCEPT ![self] = _c149]
             /\ pc' = [pc EXCEPT ![self][3] = "Done"]
             /\ x' = x

w(self) ==  \/ Clear1(self) \/ Send1(self) \/ Br1(self) \/ Rc1(self)

Next == (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-bb45834cdaac644b17aeaf05be173ce7


=========================================================
