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
channels chan[NS];

process ( w \in Nodes )
variable c = 4;
fifo fifs[NN];
{
	Lab:
	  c := c+1;
	Snd:
    send(fifs[1], "msg");
	\* Snd2:
    \* send(chan[self], "msg");
	Rcv:
	  receive(fifs[1], cur);
	\* Rcv2:
	  \* receive(chan[self], cur);
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-03383e423661db76e49bb9146e1d50c4
VARIABLES cur, chan, pc, c, fifs

vars == << cur, chan, pc, c, fifs >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n430 \in NS |-> {}]
        (* Process w *)
        /\ c = [self \in Nodes |-> 4]
        /\ fifs = [self \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Lab">>]

Lab(self) == /\ pc[self][1]  = "Lab"
             /\ c' = [c EXCEPT ![self] = c[self]+1]
             /\ pc' = [pc EXCEPT ![self][1] = "Snd"]
             /\ UNCHANGED << cur, chan, fifs >>

Snd(self) == /\ pc[self][1]  = "Snd"
             /\ fifs' = [fifs EXCEPT ![self][1] =  Append(@, "msg")]
             /\ pc' = [pc EXCEPT ![self][1] = "Rcv"]
             /\ UNCHANGED << cur, chan, c >>

Rcv(self) == /\ pc[self][1]  = "Rcv"
             /\ Len(fifs[self][1]) > 0 
             /\ cur' = Head(fifs[self][1])
             /\ fifs' = [fifs EXCEPT ![self][1] =  Tail(@) ]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << chan, c >>

w(self) == Lab(self) \/ Snd(self) \/ Rcv(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-aa457ff36bec2755196a17fa98fe2df7
==========================================================

