------------------------ MODULE OneProcessSendChannel -------------------------
EXTENDS TLC, Integers, Sequences

N == 3
Nodes == 1..N-1
NNodes == N..5

(* PlusCal options (-label -distpcal -setchannels) *)

(*--algorithm dummy  {
variables c = 2, r = 22, TO = {<<1,1>>, <<2,2>>};
channels ch, ch1[Nodes],ch2[Nodes][Nodes];

process ( sid = 3 )
variable cur = 10, loc = 0;
{
    Send1:
    send(ch,cur);
    send(ch1[1],cur);
    send(ch2[2,2],cur);
    SendM1:
    multicast(ch1,[ag \in DOMAIN ch1 |-> ag]);
    SendM2:
    multicast(ch2,[n = 1, m \in Nodes |-> n]);
}
{
    R1:
    receive(ch,loc);
    R1a:
    receive(ch1[1],loc);
    R1b:
    receive(ch2[2,2],loc);
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "404a7804" /\ chksum(tla) = "d2f187bb")
VARIABLES c, r, TO, ch, ch1, ch2, pc, cur, loc

vars == << c, r, TO, ch, ch1, ch2, pc, cur, loc >>

ProcSet == {3}

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ c = 2
        /\ r = 22
        /\ TO = {<<1,1>>, <<2,2>>}
        /\ ch = {}
        /\ ch1 = [_n20 \in  Nodes |-> {}]
        /\ ch2 = [_n30 \in  Nodes, _n41 \in  Nodes |-> {}]
        (* Process sid *)
        /\ cur = 10
        /\ loc = 0
        /\ pc = [self \in ProcSet |-> <<"Send1","R1">>]

Send1 == /\ pc[3][1]  = "Send1"
         /\ ch' = (ch \cup {cur})
         /\ ch1' = [ch1 EXCEPT ![1] = @ \cup {cur}]
         /\ ch2' = [ch2 EXCEPT ![2,2] = @ \cup {cur}]
         /\ pc' = [pc EXCEPT ![3][1] = "SendM1"]
         /\ UNCHANGED << c, r, TO, cur, loc >>

SendM1 == /\ pc[3][1]  = "SendM1"
          /\ ch1' = [ag \in DOMAIN ch1 |->  IF ag \in DOMAIN ch1
                     THEN ch1[ag] \cup {ag} 
                     ELSE ch1[ag]]
          /\ pc' = [pc EXCEPT ![3][1] = "SendM2"]
          /\ UNCHANGED << c, r, TO, ch, ch2, cur, loc >>

SendM2 == /\ pc[3][1]  = "SendM2"
          /\ ch2' = [<<n, m>> \in DOMAIN ch2 |->  IF n = 1 /\ m \in Nodes
                     THEN ch2[n, m] \cup {n} 
                     ELSE ch2[n, m]]
          /\ pc' = [pc EXCEPT ![3][1] = "Done"]
          /\ UNCHANGED << c, r, TO, ch, ch1, cur, loc >>

sid1 == Send1 \/ SendM1 \/ SendM2

R1 == /\ pc[3][2]  = "R1"
      /\ \E _c1210 \in ch:
           /\ ch' = ch \ {_c1210}
           /\ loc' = _c1210
      /\ pc' = [pc EXCEPT ![3][2] = "R1a"]
      /\ UNCHANGED << c, r, TO, ch1, ch2, cur >>

R1a == /\ pc[3][2]  = "R1a"
       /\ \E _c1214 \in ch1[1]:
            /\ ch1' = [ch1 EXCEPT ![1] = @ \ {_c1214}]
            /\ loc' = _c1214
       /\ pc' = [pc EXCEPT ![3][2] = "R1b"]
       /\ UNCHANGED << c, r, TO, ch, ch2, cur >>

R1b == /\ pc[3][2]  = "R1b"
       /\ \E _c1225 \in ch2[2,2]:
            /\ ch2' = [ch2 EXCEPT ![2,2] = @ \ {_c1225}]
            /\ loc' = _c1225
       /\ pc' = [pc EXCEPT ![3][2] = "Done"]
       /\ UNCHANGED << c, r, TO, ch, ch1, cur >>

sid2 == R1 \/ R1a \/ R1b

sid == sid1 \/ sid2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 
================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}
