------------------------ MODULE VarAndChannelDecls1C -------------------------
EXTENDS TLC, Integers, Sequences

N == 2
Nodes == 1 .. 3
NN == 1 .. 2
NS == 1 .. 4

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
channels chan[NS, NS];

process ( w \in Nodes )
variable c = 4;
channel fifs[NN];
{
	Lab:
	  c := c+1;
	Snd:
    send(fifs[1], "msg");
	Snd2:
     send(chan[self, self], "msg");
        BROAD:
                broadcast(fifs, "abc");	
        Rcv:
	  receive(fifs[1], cur);
	\* Rcv2:
	  \* receive(chan[self], cur);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ac2fb404a643f705dae522f4b10b25ca
VARIABLES cur, chan, pc, c, fifs

vars == << cur, chan, pc, c, fifs >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_mn430 \in NS, _mn441 \in NS |-> {}]
        (* Process w *)
        /\ c = [self \in Nodes |-> 4]
        /\ fifs = [_nmd438 \in Nodes |-> [_nmd498 \in NN |-> {}]]
        /\ pc = [self \in ProcSet |-> <<"Lab">>]

Lab(self) == /\ pc[self][1]  = "Lab"
             /\ c' = [c EXCEPT ![self] = c[self]+1]
             /\ pc' = [pc EXCEPT ![self][1] = "Snd"]
             /\ UNCHANGED << cur, chan, fifs >>

Snd(self) == /\ pc[self][1]  = "Snd"
             /\ fifs' = [fifs EXCEPT ![self][1] = fifs[self][1] \cup {"msg"}]
             /\ pc' = [pc EXCEPT ![self][1] = "Snd2"]
             /\ UNCHANGED << cur, chan, c >>

Snd2(self) == /\ pc[self][1]  = "Snd2"
              /\ chan' = [chan EXCEPT ![self, self] = chan[self, self] \cup {"msg"}]
              /\ pc' = [pc EXCEPT ![self][1] = "BROAD"]
              /\ UNCHANGED << cur, c, fifs >>

BROAD(self) == /\ pc[self][1]  = "BROAD"
               /\ fifs' = [fifs EXCEPT ![self] = [_n0 \in NN |-> fifs[_n0] \cup {"abc"}]]
               /\ pc' = [pc EXCEPT ![self][1] = "Rcv"]
               /\ UNCHANGED << cur, chan, c >>

Rcv(self) == /\ pc[self][1]  = "Rcv"
             /\ \E _f199 \in fifs[self][1]:
                  /\ cur' = _f199
                  /\ fifs' = [fifs EXCEPT ![self][1] = fifs[self][1] \ {_f199}]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << chan, c >>

w(self) == Lab(self) \/ Snd(self) \/ Snd2(self) \/ BROAD(self) \/ Rcv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c7c666b9c7b8e64d29bb715c0d8710ed
==========================================================
