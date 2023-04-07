------------------------ MODULE TwoProcessesGlobalChannelBUG -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ (Nodes \cup {Id}) -> 0..2 ],  
          cur = "none";

channels ch[Nodes \cup {Id}], ch2[Nodes][Nodes];

process ( qid = Id )
{
    QL:
	receive(ch[Id], ar[1]); (* BUG: array destination *)
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "dccfdf96" /\ chksum(tla) = "c37207de")
VARIABLES ar, cur, ch, ch2, pc

vars == << ar, cur, ch, ch2, pc >>

ProcSet == {Id}

SubProcSet == [_n1 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ ar = [ (Nodes \cup {Id}) -> 0..2 ]
        /\ cur = "none"
        /\ ch = [_n20 \in  Nodes \cup { Id } |-> {}]
        /\ ch2 = [_n30 \in  Nodes, _n41 \in  Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> <<"QL">>]

QL == /\ pc[Id][1]  = "QL"
      /\ \E _c1410 \in ch[Id]:
           /\ ar' = [ar EXCEPT ![1] = _c1410]
           /\ ch' = [ch EXCEPT ![Id] = @ \ {_c1410}]
      /\ pc' = [pc EXCEPT ![Id][1] = "Done"]
      /\ UNCHANGED << cur, ch2 >>

qid1 == QL

qid == qid1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == qid
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

