------------------------ MODULE TwoProcessesGlobalChannel -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ (Nodes \cup {Id}) -> 0..2 ],  
          cur = "none";

channels ch[Nodes \cup {Id}], ch2[Nodes][Nodes];
fifo fi[Nodes \cup {Id}];

process ( pid \in Nodes )
variable c = 3;
{
    PL:
	c := c+1;
    send(ch[Id], c);
}

process ( qid = Id )
variable d = 4;
{
    QL:
	receive(ch[Id], d);
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "35920b30" /\ chksum(tla) = "cda6ae5c")
VARIABLES ar, cur, ch, ch2, fi, pc, c, d

vars == << ar, cur, ch, ch2, fi, pc, c, d >>

ProcSet == (Nodes) \cup {Id}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in Nodes THEN 1..1
                                 ELSE (**Id**) 1..1]

Init == (* Global variables *)
        /\ ar = [ (Nodes \cup {Id}) -> 0..2 ]
        /\ cur = "none"
        /\ ch = [_n20 \in  Nodes \cup { Id } |-> {}]
        /\ ch2 = [_n30 \in  Nodes, _n41 \in  Nodes |-> {}]
        /\ fi = [_n50 \in  Nodes \cup { Id } |-> <<>>]
        (* Process pid *)
        /\ c = [self \in Nodes |-> 3]
        (* Process qid *)
        /\ d = 4
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"PL">>
                                        [] self = Id -> <<"QL">>]

PL(self) == /\ pc[self][1]  = "PL"
            /\ c' = [c EXCEPT ![self] = c[self]+1]
            /\ ch' = [ch EXCEPT ![Id] = @ \cup {c'[self]}]
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ UNCHANGED << ar, cur, ch2, fi, d >>

pid1(self) == PL(self)

pid(self) == pid1(self)

QL == /\ pc[Id][1]  = "QL"
      /\ \E _c1410 \in ch[Id]:
           /\ ch' = [ch EXCEPT ![Id] = @ \ {_c1410}]
           /\ d' = _c1410
      /\ pc' = [pc EXCEPT ![Id][1] = "Done"]
      /\ UNCHANGED << ar, cur, ch2, fi, c >>

qid1 == QL

qid == qid1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == qid
           \/ (\E self \in Nodes: pid(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 
==========================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}

