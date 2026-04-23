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
\* BEGIN TRANSLATION (chksum(pcal) = "ca0639e5" /\ chksum(tla) = "13ec7bd2")
VARIABLES c, r, ch, ch1, ch2, pc, cur, loc, cc

vars == << c, r, ch, ch1, ch2, pc, cur, loc, cc >>

ProcSet == (Nodes) \cup {N+1}

SubProcSet == [self \in ProcSet |->  CASE self \in Nodes -> 1..2
                                     []   self = N+1 -> 1..1 ]

Init == (* Global variables *)
        /\ c = 2
        /\ r = 22
        /\ ch = EmptyBag
        /\ ch1 = [_n10 \in  Nodes |-> EmptyBag]
        /\ ch2 = [_n20 \in  Nodes, _n31 \in  Nodes |-> EmptyBag]
        (* Process sid *)
        /\ cur = [self \in Nodes |-> 10]
        /\ loc = [self \in Nodes |-> 0]
        (* Process qid *)
        /\ cc = 10
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> <<"Send1","R1">>
                                        [] self = N+1 -> <<"Lbl_1">>]

Send1(self) == /\ pc[self][1]  = "Send1"
               /\ ch' = ch (+) SetToBag({cur[self]})
               /\ ch1' = [ch1 EXCEPT ![1] = @ (+) SetToBag({cur[self]})]
               /\ ch2' = [ch2 EXCEPT ![2,2] = @ (+) SetToBag({cur[self]})]
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << c, r, cur, loc, cc >>

sid_thread_1(self) == Send1(self)

R1(self) == /\ pc[self][2]  = "R1"
            /\ \E __c1__ \in DOMAIN ch:
                 /\ ch' = ch (-) SetToBag({__c1__})
                 /\ loc' = [loc EXCEPT ![self] = __c1__]
            /\ pc' = [pc EXCEPT ![self][2] = "R1a"]
            /\ UNCHANGED << c, r, ch1, ch2, cur, cc >>

R1a(self) == /\ pc[self][2]  = "R1a"
             /\ \E __c2__ \in DOMAIN ch1[1]:
                  /\ ch1' = [ch1 EXCEPT ![1] = @ (-) SetToBag({__c2__})]
                  /\ loc' = [loc EXCEPT ![self] = __c2__]
             /\ pc' = [pc EXCEPT ![self][2] = "R1b"]
             /\ UNCHANGED << c, r, ch, ch2, cur, cc >>

R1b(self) == /\ pc[self][2]  = "R1b"
             /\ \E __c3__ \in DOMAIN ch2[2,2]:
                  /\ ch2' = [ch2 EXCEPT ![2,2] = @ (-) SetToBag({__c3__})]
                  /\ loc' = [loc EXCEPT ![self] = __c3__]
             /\ pc' = [pc EXCEPT ![self][2] = "Done"]
             /\ UNCHANGED << c, r, ch, ch1, cur, cc >>

sid_thread_2(self) == R1(self) \/ R1a(self) \/ R1b(self)

sid(self) == sid_thread_1(self) \/ sid_thread_2(self)

Lbl_1 == /\ pc[N+1][1]  = "Lbl_1"
         /\ cc' = cc + 2
         /\ pc' = [pc EXCEPT ![N+1][1] = "Done"]
         /\ UNCHANGED << c, r, ch, ch1, ch2, cur, loc >>

qid_thread_1 == Lbl_1

qid == qid_thread_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == qid
           \/ (\E self \in Nodes: sid(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}
