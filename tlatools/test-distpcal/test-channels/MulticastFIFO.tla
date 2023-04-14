------------------------ MODULE MulticastFIFO -------------------------
EXTENDS TLC, Integers, Sequences

N == 3
Nodes == 1..N-1
NNodes == N..5

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2, r = 22, TO = {<<1,1>>, <<2,2>>};
fifos ch1[Nodes],ch2[Nodes][Nodes];

process ( sid = 3 )
variable cur = 1, loc = 0;
{
    SendM1:
    multicast(ch1,[ag \in DOMAIN ch1 |-> ag]);
    multicast(ch1,[ag \in DOMAIN ch1 |-> ag]);
    SendM2:
    multicast(ch2,[n = 1, m \in Nodes |-> n]);
    multicast(ch2,[n \in 
    Nodes, m \in Nodes |-> n 
     + 1]);
    multicast(ch2,[ag \in Nodes \X Nodes |-> 10]);
    multicast(ch2,[ag \in TO |-> 0]);
    After:
    cur := cur + 1;
}

process ( w \in Nodes )
variable loc = 0;
{
    R:
    receive(ch1[self],loc);
}
{
    Rb:
    receive(ch1[self],loc);
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c408ba2d" /\ chksum(tla) = "4ebebae2")
\* Process variable loc of process sid at line 15 col 19 changed to loc_
VARIABLES c, r, TO, ch1, ch2, pc, cur, loc_, loc

vars == << c, r, TO, ch1, ch2, pc, cur, loc_, loc >>

ProcSet == {3} \cup (Nodes)

SubProcSet == [_n1 \in ProcSet |-> IF _n1 = 3 THEN 1..1
                               ELSE (**Nodes**) 1..2]

Init == (* Global variables *)
        /\ c = 2
        /\ r = 22
        /\ TO = {<<1,1>>, <<2,2>>}
        /\ ch1 = [_n20 \in  Nodes |-> <<>>]
        /\ ch2 = [_n30 \in  Nodes, _n41 \in  Nodes |-> <<>>]
        (* Process sid *)
        /\ cur = 1
        /\ loc_ = 0
        (* Process w *)
        /\ loc = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 3 -> <<"SendM1">>
                                        [] self \in Nodes -> <<"R","Rb">>]

SendM1 == /\ pc[3][1]  = "SendM1"
          /\ ch1' = [ag \in DOMAIN ch1 |->  IF ag \in DOMAIN ch1
                     THEN  Append(ch1[ag], ag)
                     ELSE ch1[ag]]
          /\ pc' = [pc EXCEPT ![3][1] = "Lbl_1"]
          /\ UNCHANGED << c, r, TO, ch2, cur, loc_, loc >>

Lbl_1 == /\ pc[3][1]  = "Lbl_1"
         /\ ch1' = [ag \in DOMAIN ch1 |->  IF ag \in DOMAIN ch1
                    THEN  Append(ch1[ag], ag)
                    ELSE ch1[ag]]
         /\ pc' = [pc EXCEPT ![3][1] = "SendM2"]
         /\ UNCHANGED << c, r, TO, ch2, cur, loc_, loc >>

SendM2 == /\ pc[3][1]  = "SendM2"
          /\ ch2' = [<<n, m>> \in DOMAIN ch2 |->  IF n = 1 /\ m \in Nodes
                     THEN  Append(ch2[n, m], n)
                     ELSE ch2[n, m]]
          /\ pc' = [pc EXCEPT ![3][1] = "Lbl_2"]
          /\ UNCHANGED << c, r, TO, ch1, cur, loc_, loc >>

Lbl_2 == /\ pc[3][1]  = "Lbl_2"
         /\ ch2' = [<<n, m>> \in DOMAIN ch2 |->  IF n \in Nodes /\ m \in Nodes
                    THEN  Append(ch2[n, m], n+1)
                    ELSE ch2[n, m]]
         /\ pc' = [pc EXCEPT ![3][1] = "Lbl_3"]
         /\ UNCHANGED << c, r, TO, ch1, cur, loc_, loc >>

Lbl_3 == /\ pc[3][1]  = "Lbl_3"
         /\ ch2' = [ag \in DOMAIN ch2 |->  IF ag \in Nodes \X Nodes
                    THEN  Append(ch2[ag], 10)
                    ELSE ch2[ag]]
         /\ pc' = [pc EXCEPT ![3][1] = "Lbl_4"]
         /\ UNCHANGED << c, r, TO, ch1, cur, loc_, loc >>

Lbl_4 == /\ pc[3][1]  = "Lbl_4"
         /\ ch2' = [ag \in DOMAIN ch2 |->  IF ag \in TO
                    THEN  Append(ch2[ag], 0)
                    ELSE ch2[ag]]
         /\ pc' = [pc EXCEPT ![3][1] = "After"]
         /\ UNCHANGED << c, r, TO, ch1, cur, loc_, loc >>

After == /\ pc[3][1]  = "After"
         /\ cur' = cur + 1
         /\ pc' = [pc EXCEPT ![3][1] = "Done"]
         /\ UNCHANGED << c, r, TO, ch1, ch2, loc_, loc >>

sid1 == SendM1 \/ Lbl_1 \/ SendM2 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ After

sid == sid1

R(self) == /\ pc[self][1]  = "R"
           /\ Len(ch1[self]) > 0 
           /\ loc' = [loc EXCEPT ![self] = Head(ch1[self])]
           /\ ch1' = [ch1 EXCEPT ![self] =  Tail(@) ]
           /\ pc' = [pc EXCEPT ![self][1] = "Done"]
           /\ UNCHANGED << c, r, TO, ch2, cur, loc_ >>

w1(self) == R(self)

Rb(self) == /\ pc[self][2]  = "Rb"
            /\ Len(ch1[self]) > 0 
            /\ loc' = [loc EXCEPT ![self] = Head(ch1[self])]
            /\ ch1' = [ch1 EXCEPT ![self] =  Tail(@) ]
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]
            /\ UNCHANGED << c, r, TO, ch2, cur, loc_ >>

w2(self) == Rb(self)

w(self) == w1(self) \/ w2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == sid
           \/ (\E self \in Nodes: w(self))
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
