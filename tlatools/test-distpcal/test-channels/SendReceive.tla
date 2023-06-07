------------------------ MODULE SendReceive -------------------------
EXTENDS TLC, Integers, Sequences, Bags

N == 2
Nodes == 1..N

(* PlusCal options (-label -distpcal ) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch, ch1[Nodes],ch2[Nodes][Nodes];

process ( sid \in Nodes )
variable cur = 10, loc = 0;
{
    Send1:
    send(ch,cur);
    send(ch1[1],cur);
    send(ch2[2,2],cur);
}
{
    R1:
    receive(ch,loc);
    R1a:
    receive(ch1[1],loc);
    R1b:
    receive(ch2[2,2],loc);
}

process ( qid = N+1 )
variable cc = 10;
{
    cc := cc + 2;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2b1c0734" /\ chksum(tla) = "be97162d")
VARIABLES c, r, ch, ch1, ch2, pc, cur, loc, cc

vars == << c, r, ch, ch1, ch2, pc, cur, loc, cc >>

ProcSet == (Nodes) \cup {N+1}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in Nodes THEN 1..2
                                   ELSE (** _n1 = N+1 **) 1..1]

Init == (* Global variables *)
        /\ c = 2
        /\ r = 22
        /\ ch = <<>>
        /\ ch1 = [_n20 \in  Nodes |-> <<>>]
        /\ ch2 = [_n30 \in  Nodes, _n41 \in  Nodes |-> <<>>]
        (* Process sid *)
        /\ cur = [self \in Nodes |-> 10]
        /\ loc = [self \in Nodes |-> 0]
        (* Process qid *)
        /\ cc = 10
        /\ pc = [self \in ProcSet |-> IF self \in Nodes THEN <<"Send1","R1">>
                                        ELSE <<"Lbl_1">>]

Send1(self) == /\ pc[self][1]  = "Send1"
               /\ ch' = ch (+) [__v1__ \in {cur[self]} |-> 1]
               /\ ch1' = [ch1 EXCEPT ![1] = @ (+) [__v2__ \in {cur[self]} |-> 1]]
               /\ ch2' = [ch2 EXCEPT ![2,2] = @ (+) [__v3__ \in {cur[self]} |-> 1]]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << c, r, cur, loc, cc >>

sid1(self) == Send1(self)

R1(self) == /\ pc[self][2]  = "R1"
            /\ \E __c4__ \in DOMAIN ch:
                 /\ ch' = ch (-) [__v5__ \in {__c4__} |-> 1]
                 /\ loc' = [loc EXCEPT ![self] = ch[__c4__]]
            /\ pc' = [pc EXCEPT ![self][2] = "R1a"]
            /\ UNCHANGED << c, r, ch1, ch2, cur, cc >>

R1a(self) == /\ pc[self][2]  = "R1a"
             /\ \E __c6__ \in DOMAIN ch1[1]:
                  /\ ch1' = [ch1 EXCEPT ![1] = @ (-) [__v7__ \in {__c6__} |-> 1]]
                  /\ loc' = [loc EXCEPT ![self] = ch1[1][__c6__]]
             /\ pc' = [pc EXCEPT ![self][2] = "R1b"]
             /\ UNCHANGED << c, r, ch, ch2, cur, cc >>

R1b(self) == /\ pc[self][2]  = "R1b"
             /\ \E __c8__ \in DOMAIN ch2[2,2]:
                  /\ ch2' = [ch2 EXCEPT ![2,2] = @ (-) [__v9__ \in {__c8__} |-> 1]]
                  /\ loc' = [loc EXCEPT ![self] = ch2[2,2][__c8__]]
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]
             /\ UNCHANGED << c, r, ch, ch1, cur, cc >>

sid2(self) == R1(self) \/ R1a(self) \/ R1b(self)

sid(self) == sid1(self) \/ sid2(self)

Lbl_1 == /\ pc[N+1][1]  = "Lbl_1"
         /\ cc' = cc + 2
         /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
         /\ UNCHANGED << c, r, ch, ch1, ch2, cur, loc >>

qid1 == Lbl_1

qid == qid1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == qid
           \/ (\E self \in Nodes: sid(self))
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
