------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

fifo chan;

process (x \in Nodes)
variable i = "none";
{
    Add:
        send(chan, "msg");
} {
    Rec:
        receive(chan, i);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-10cb47ac85519825af433a198b3d5cf1
VARIABLES chan, pc, i

vars == << chan, pc, i >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = <<>>
        (* Process x *)
        /\ i = [self \in Nodes |-> "none"]
        /\ pc = [self \in ProcSet |-> <<"Add","Rec">>]

Add(self) == /\ pc[self] [1] = "Add"
             /\ chan' =  Append(chan, "msg")
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ i' = i

Rec(self) == /\ pc[self] [2] = "Rec"
             /\ Len(chan) > 0 
             /\ i' = [i EXCEPT ![self] = Head(chan)]
             /\ chan' =  Tail(chan)
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]

x(self) ==  \/ Add(self) \/ Rec(self)

Next == (\E self \in Nodes: x(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-dd761a0b52be12fe5c676ddd923de47b




=========================================================
