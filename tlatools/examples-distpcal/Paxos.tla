------------------------------- MODULE Paxos ---------------------------------
(****************************************************************************)
(* This is a representation of the core of the Paxos consensus algorithm in *)
(* Distributed PlusCal. Every node may play the role of leader, acceptor,   *)
(* and learner. Leader election is not modeled: any process that suspects   *)
(* the current leader to have crashed may initiate a new ballot.            *)
(****************************************************************************)
EXTENDS Integers, Bags

CONSTANTS
  N,          \* number of nodes
  Values      \* set of values that may be proposed / chosen

Nodes == 1 .. N
quorum == N \div 2
None == CHOOSE none : none \notin Values


(****************************************************************************)
(* Ballots are pairs of natural numbers and node IDs where the latter       *)
(* indicates the node at the origin of the ballot. Therefore, ballots       *)
(* initiated by different nodes can be differentiated. Ballot IDs are       *)
(* ordered lexicographically.                                               *)
(****************************************************************************)
Ballots == Nat \X Nodes  \* override definition for finite-state model checking
less(b1, b2) ==
   \/ b1[1] < b2[1]
   \/ b1[1] = b2[1] /\ b1[2] < b2[2]

(* PlusCal options (-label -distpcal) *)

(*--algorithm Paxos {

  channels ch[Nodes];

  process (node \in Nodes)
  variables
     \* the highest-number ballot the node has participated in
     maxBal = <<0,self>>,
     \* the highest-number ballot in which the node has voted
     maxVBal = <<0,self>>,
     \* the value the node voted for in that ballot
     maxVal = None,
     \* last message received (None unless handling a message)
     msg = None,
     \* ballot number used in latest "1a" message
     ballot1a = <<0,self>>,
     \* number of replies received by a leader to its "1a" message
     replies1a = 0,
     \* the highest maxVBal value the leader heard of
     maxVBalRcvd = <<0,self>>,
     \* the corresponding value
     maxValRcvd = None,
     \* bag of votes received by the node
     votesRcvd = EmptyBag,
     \* value chosen by the node
     chosen = None;
  {  \* main thread of node
n0:  while (TRUE) {
        either {
           \* suspect the current leader to have crashed, start new ballot
           with (newBallot = << maxBal[1]+1, self >>) {
              multicast(ch, [n \in Nodes \ {self} |->
                               [type |-> "1a", leader |-> self,
                                bal |-> newBallot] ] );
              maxBal := newBallot;
              ballot1a := newBallot;
              replies1a := 1; \* leader implicitly replies to its own message
              maxVBalRcvd := maxVBal;
              maxValRcvd := maxVal;
           }
        }
        or {
           \* received messages from a quorum of nodes in reply to "1a" message
           when (replies1a > quorum);
           \* if some reply contained a value, take the one in the reply for
           \* the highest ballot, otherwise choose any value
           with (v \in {v \in Values : maxValRcvd = None \/ v = maxValRcvd}) {
             multicast(ch, [n \in Nodes \ {self} |->
                              [type |-> "2a", leader |-> self,
                               bal |-> ballot1a, val |-> v]]);
           };
           \* stop handling "1b" messages and reset corresponding variables
           replies1a := 0;
           ballot1a := <<0,self>>;
           maxVBalRcvd := <<0,self>>;
           maxValRcvd := None;
        }
        or {
           \* learn a value when a quorum of nodes voted for it
           with (v \in {v \in Values : \E b \in Ballots :
                          CopiesIn([bal |-> b, val |-> v], votesRcvd)
                          > quorum}) {
              chosen := v;
           }
        }
     }
  }  \* end main thread
  {  \* helper thread for receiving messages
r0:  while (TRUE) {
        receive(ch[self], msg);
        if (msg.type = "1a" /\ less(maxBal, msg.bal)) {
           \* node participates in new ballot
           maxBal := msg.bal;
           send(ch[msg.leader],
                     [type |-> "1b", bal |-> msg.bal,
                      maxVBal |-> maxVBal, maxVal |-> maxVal]);
           msg := None;  \* reset to default value (reduce state space)
        }
        else if (msg.type = "1b" /\ msg.bal = ballot1a /\ replies1a > 0) {
           \* leader receives a reply to its previous "1a" message
           \* NB: replies1a = 0 means that the leader is no longer interested in "1b"
           \* messages because it has already sent a "2a" message.
           replies1a := replies1a + 1;
           \* record highest maxVBal value (if any) and corresponding value
           if (msg.maxVBal[1] # 0 /\ less(maxVBalRcvd, msg.maxVBal)) {
              maxVBalRcvd := msg.maxVBal; maxValRcvd := msg.maxVal;
           };
           msg := None;
        }
        else if (msg.type = "2a" /\ (less(maxBal, msg.bal) \/ maxBal = msg.bal) /\ maxVBal # msg.bal) {
           maxBal := msg.bal;
           maxVBal := msg.bal;
           maxVal := msg.val;
           \* vote for value contained in "2a" message
           multicast(ch, [n \in Nodes \ {self} |->
                            [type |-> "2b",
                             bal |-> msg.bal, val |-> msg.val]]);
           \* record the node's vote
           votesRcvd := votesRcvd (+)
                        SetToBag({[bal |-> msg.bal, val |-> msg.val]});
           msg := None;
        }
        else if (msg.type = "2b") {
           \* record vote
           votesRcvd := votesRcvd (+)
                        SetToBag({[bal |-> msg.bal, val |-> msg.val]});
           msg := None;
        }
        else {
           msg := None;
        }
     }  \* end helper thread
  }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "75c82728" /\ chksum(tla) = "cc812100")
VARIABLES ch, pc, maxBal, maxVBal, maxVal, msg, ballot1a, replies1a, 
          maxVBalRcvd, maxValRcvd, votesRcvd, chosen

vars == << ch, pc, maxBal, maxVBal, maxVal, msg, ballot1a, replies1a, 
           maxVBalRcvd, maxValRcvd, votesRcvd, chosen >>

ProcSet == (Nodes)

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ ch = [_n20 \in  Nodes |-> <<>>]
        (* Process node *)
        /\ maxBal = [self \in Nodes |-> <<0,self>>]
        /\ maxVBal = [self \in Nodes |-> <<0,self>>]
        /\ maxVal = [self \in Nodes |-> None]
        /\ msg = [self \in Nodes |-> None]
        /\ ballot1a = [self \in Nodes |-> <<0,self>>]
        /\ replies1a = [self \in Nodes |-> 0]
        /\ maxVBalRcvd = [self \in Nodes |-> <<0,self>>]
        /\ maxValRcvd = [self \in Nodes |-> None]
        /\ votesRcvd = [self \in Nodes |-> EmptyBag]
        /\ chosen = [self \in Nodes |-> None]
        /\ pc = [self \in ProcSet |-> <<"n0","r0">>]

n0(self) == /\ pc[self][1]  = "n0"
            /\ \/ /\ LET newBallot == << maxBal[self][1]+1, self >> IN
                       /\ ch' = [n \in DOMAIN ch |->  IF n \in Nodes \ { self }
                                 THEN ch[n] (+) SetToBag({[type|->"1a",leader|->self,bal|->newBallot]})
                                 ELSE ch[n]]
                       /\ maxBal' = [maxBal EXCEPT ![self] = newBallot]
                       /\ ballot1a' = [ballot1a EXCEPT ![self] = newBallot]
                       /\ replies1a' = [replies1a EXCEPT ![self] = 1]
                       /\ maxVBalRcvd' = [maxVBalRcvd EXCEPT ![self] = maxVBal[self]]
                       /\ maxValRcvd' = [maxValRcvd EXCEPT ![self] = maxVal[self]]
                  /\ UNCHANGED chosen
               \/ /\ (replies1a[self] > quorum)
                  /\ \E v \in {v \in Values : maxValRcvd[self] = None \/ v = maxValRcvd[self]}:
                       ch' = [n \in DOMAIN ch |->  IF n \in Nodes \ { self }
                              THEN ch[n] (+) SetToBag({[type|->"2a",leader|->self,bal|->ballot1a[self],val|->v]})
                                    ELSE ch[n]]
                  /\ replies1a' = [replies1a EXCEPT ![self] = 0]
                  /\ ballot1a' = [ballot1a EXCEPT ![self] = <<0,self>>]
                  /\ maxVBalRcvd' = [maxVBalRcvd EXCEPT ![self] = <<0,self>>]
                  /\ maxValRcvd' = [maxValRcvd EXCEPT ![self] = None]
                  /\ UNCHANGED <<maxBal, chosen>>
               \/ /\ \E v \in {v \in Values : \E b \in Ballots :
                                 CopiesIn([bal |-> b, val |-> v], votesRcvd[self])
                                 > quorum}:
                       chosen' = [chosen EXCEPT ![self] = v]
                  /\ UNCHANGED <<ch, maxBal, ballot1a, replies1a, maxVBalRcvd, maxValRcvd>>
            /\ pc' = [pc EXCEPT ![self][1] = "n0"]
            /\ UNCHANGED << maxVBal, maxVal, msg, votesRcvd >>

node1(self) == n0(self)

r0(self) == /\ pc[self][2]  = "r0"
            /\ \E __c1__ \in DOMAIN ch[self]:
                 /\ ch' = [ch EXCEPT ![self] = @ (-) SetToBag({__c1__})]
                 /\ msg' = [msg EXCEPT ![self] = __c1__]
            /\ IF msg'[self].type = "1a" /\ less(maxBal[self], msg'[self].bal)
                  THEN /\ maxBal' = [maxBal EXCEPT ![self] = msg'[self].bal]
                       /\ pc' = [pc EXCEPT ![self][2] = "Lbl_1"]
                       /\ UNCHANGED << maxVBal, maxVal, replies1a, maxVBalRcvd, 
                                       maxValRcvd, votesRcvd >>
                  ELSE /\ IF msg'[self].type = "1b" /\ msg'[self].bal = ballot1a[self] /\ replies1a[self] > 0
                             THEN /\ replies1a' = [replies1a EXCEPT ![self] = replies1a[self] + 1]
                                  /\ IF msg'[self].maxVBal[1] # 0 /\ less(maxVBalRcvd[self], msg'[self].maxVBal)
                                        THEN /\ maxVBalRcvd' = [maxVBalRcvd EXCEPT ![self] = msg'[self].maxVBal]
                                             /\ maxValRcvd' = [maxValRcvd EXCEPT ![self] = msg'[self].maxVal]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << maxVBalRcvd, 
                                                             maxValRcvd >>
                                  /\ pc' = [pc EXCEPT ![self][2] = "Lbl_2"]
                                  /\ UNCHANGED << maxBal, maxVBal, maxVal, 
                                                  votesRcvd >>
                             ELSE /\ IF msg'[self].type = "2a" /\ (less(maxBal[self], msg'[self].bal) \/ maxBal[self] = msg'[self].bal) /\ maxVBal[self] # msg'[self].bal
                                        THEN /\ maxBal' = [maxBal EXCEPT ![self] = msg'[self].bal]
                                             /\ maxVBal' = [maxVBal EXCEPT ![self] = msg'[self].bal]
                                             /\ maxVal' = [maxVal EXCEPT ![self] = msg'[self].val]
                                             /\ pc' = [pc EXCEPT ![self][2] = "Lbl_3"]
                                             /\ UNCHANGED votesRcvd
                                        ELSE /\ IF msg'[self].type = "2b"
                                                   THEN /\ votesRcvd' = [votesRcvd EXCEPT ![self] = votesRcvd[self] (+)
                                                                                                    SetToBag({[bal |-> msg'[self].bal, val |-> msg'[self].val]})]
                                                        /\ pc' = [pc EXCEPT ![self][2] = "Lbl_4"]
                                                   ELSE /\ pc' = [pc EXCEPT ![self][2] = "Lbl_5"]
                                                        /\ UNCHANGED votesRcvd
                                             /\ UNCHANGED << maxBal, maxVBal, 
                                                             maxVal >>
                                  /\ UNCHANGED << replies1a, maxVBalRcvd, 
                                                  maxValRcvd >>
            /\ UNCHANGED << ballot1a, chosen >>

Lbl_1(self) == /\ pc[self][2]  = "Lbl_1"
               /\ ch' = [ch EXCEPT ![msg[self].leader] = @ (+) SetToBag({[type |-> "1b", bal |-> msg[self].bal,maxVBal |-> maxVBal[self], maxVal |-> maxVal[self]]})]
               /\ msg' = [msg EXCEPT ![self] = None]
               /\ pc' = [pc EXCEPT ![self][2] = "r0"]
               /\ UNCHANGED << maxBal, maxVBal, maxVal, ballot1a, replies1a, 
                               maxVBalRcvd, maxValRcvd, votesRcvd, chosen >>

Lbl_2(self) == /\ pc[self][2]  = "Lbl_2"
               /\ msg' = [msg EXCEPT ![self] = None]
               /\ pc' = [pc EXCEPT ![self][2] = "r0"]
               /\ UNCHANGED << ch, maxBal, maxVBal, maxVal, ballot1a, 
                               replies1a, maxVBalRcvd, maxValRcvd, votesRcvd, 
                               chosen >>

Lbl_3(self) == /\ pc[self][2]  = "Lbl_3"
               /\ ch' = [n \in DOMAIN ch |->  IF n \in Nodes \ { self }
                         THEN ch[n] (+) SetToBag({[type|->"2b",bal|->msg[self].bal,val|->msg[self].val]})
                                     ELSE ch[n]]
               /\ votesRcvd' = [votesRcvd EXCEPT ![self] = votesRcvd[self] (+)
                                                           SetToBag({[bal |-> msg[self].bal, val |-> msg[self].val]})]
               /\ msg' = [msg EXCEPT ![self] = None]
               /\ pc' = [pc EXCEPT ![self][2] = "r0"]
               /\ UNCHANGED << maxBal, maxVBal, maxVal, ballot1a, replies1a, 
                               maxVBalRcvd, maxValRcvd, chosen >>

Lbl_4(self) == /\ pc[self][2]  = "Lbl_4"
               /\ msg' = [msg EXCEPT ![self] = None]
               /\ pc' = [pc EXCEPT ![self][2] = "r0"]
               /\ UNCHANGED << ch, maxBal, maxVBal, maxVal, ballot1a, 
                               replies1a, maxVBalRcvd, maxValRcvd, votesRcvd, 
                               chosen >>

Lbl_5(self) == /\ pc[self][2]  = "Lbl_5"
               /\ msg' = [msg EXCEPT ![self] = None]
               /\ pc' = [pc EXCEPT ![self][2] = "r0"]
               /\ UNCHANGED << ch, maxBal, maxVBal, maxVal, ballot1a, 
                               replies1a, maxVBalRcvd, maxValRcvd, votesRcvd, 
                               chosen >>

node2(self) == r0(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ Lbl_4(self) \/ Lbl_5(self)

node(self) == node1(self) \/ node2(self)

Next == (\E self \in Nodes: node(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Messages ==
    [type: {"1a"}, leader: Nodes, bal: Ballots]
    \union 
    [type: {"1b"}, bal: Ballots, maxVBal: Ballots, maxVal: Values \union {None}]
    \union 
    [type: {"2a"}, leader: Nodes, bal: Ballots, val: Values]
    \union 
    [type: {"2b"}, bal: Ballots, val: Values]

TypeOK ==
    /\ \A n \in Nodes : IsABag(ch[n])
    /\ \A n \in Nodes : \A m \in DOMAIN ch[n] : m \in Messages
    /\ maxBal \in [Nodes -> Ballots]
    /\ maxVBal \in [Nodes -> Ballots]
    /\ maxVal \in [Nodes -> Values \union {None}]
    /\ ballot1a \in [Nodes -> Ballots]
    /\ replies1a \in [Nodes -> Nat]
    /\ maxVBalRcvd \in [Nodes -> Ballots]
    /\ maxValRcvd \in [Nodes -> Values \union {None}]
    /\ \A n \in Nodes : IsABag(votesRcvd[n])
    /\ \A n \in Nodes : \A v \in DOMAIN votesRcvd[n] : v \in [bal : Ballots, val : Values]
    /\ chosen \in [Nodes -> Values \union {None}]

(****************************************************************************)
(* Any two nodes that have chosen some value must agree.                    *)
(****************************************************************************)
Consistency ==
    /\ \A m,n \in Nodes : chosen[m] # None /\ chosen[n] # None 
                          => chosen[m] = chosen[n]
===============================================================================
