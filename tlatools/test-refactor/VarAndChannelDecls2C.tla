------------------------ MODULE VarAndChannelDecls2C -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. 3

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
variable cur = "none";

channel chan[Nodes];


process ( w \in Nodes )
variable c = 4;
fifos fifs[Nodes];
{
	Lab:
	  c := c+1;
	Snd:
    send(chan[self], "msg");
    send(fifs[self], "msg");
	Rcv:
	  receive(chan[self], cur);
    receive(fifs[self], cur);
}

process ( v = 5 )
variable c = 4;
channel ch[Nodes];
{
	Snd2:
    send(ch[self], "msg");
	Rcv2:
	  receive(ch[self], cur);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-46b0d726ad9431279b53518c91686993
\* Process variable c of process w at line 18 col 10 changed to c_
VARIABLES cur, chan, pc, c_, fifs, c, ch

vars == << cur, chan, pc, c_, fifs, c, ch >>

ProcSet == (Nodes) \cup {5}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Nodes THEN 1..1
                                   ELSE (**5**) 1..1]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Process w *)
        /\ c_ = [self \in Nodes |-> 4]
        /\ fifs = [self \in Nodes |-> <<>>]
        (* Process v *)
        /\ c = 4
        /\ ch = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Lab">>
                                        [] self = 5 -> <<"Snd2">>]

Lab(self) == /\ pc[self][1]  = "Lab"
             /\ c_' = [c_ EXCEPT ![self] = c_[self]+1]
             /\ pc' = [pc EXCEPT ![self][1] = "Snd"]
             /\ UNCHANGED << cur, chan, fifs, c, ch >>

Snd(self) == /\ pc[self][1]  = "Snd"
             /\ chan' = [chan EXCEPT ![self] = chan[self] \cup {"msg"}]
             /\ fifs' = [fifs EXCEPT ![self][self] =  Append(@, "msg")]
             /\ pc' = [pc EXCEPT ![self][1] = "Rcv"]
             /\ UNCHANGED << cur, c_, c, ch >>

Rcv(self) == /\ pc[self][1]  = "Rcv"
             /\ \E _c149 \in chan[self]:
                  /\ chan' = [chan EXCEPT ![self] = chan[self] \ {_c149}]
                  /\ cur' = _c149
             /\ Len(fifs[self][self]) > 0 
             /\ pc' = [pc EXCEPT ![self][1] = "Lbl_1"]
             /\ UNCHANGED << c_, fifs, c, ch >>

Lbl_1(self) == /\ pc[self][1]  = "Lbl_1"
               /\ cur' = Head(fifs[self][self])
               /\ fifs' = [fifs EXCEPT ![self][self] =  Tail(@) ]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << chan, c_, c, ch >>

w(self) == Lab(self) \/ Snd(self) \/ Rcv(self) \/ Lbl_1(self)

Snd2 == /\ pc[5][1]  = "Snd2"
        /\ ch' = [ch EXCEPT ![self] = ch[self] \cup {"msg"}]
        /\ pc' = [pc EXCEPT ![5][1] = "Rcv2"]
        /\ UNCHANGED << cur, chan, c_, fifs, c >>

Rcv2 == /\ pc[5][1]  = "Rcv2"
        /\ \E _c339 \in ch[self]:
             /\ ch' = [ch EXCEPT ![self] = ch[self] \ {_c339}]
             /\ cur' = _c339
        /\ pc' = [pc EXCEPT ![5][1] = "Done"]
        /\ UNCHANGED << chan, c_, fifs, c >>

v == Snd2 \/ Rcv2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == v
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-66f93c8d723524a7b7c1337384e02984
==========================================================

