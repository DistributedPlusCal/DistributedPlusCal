---------------------------- MODULE lm ----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME N \in Nat 

Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(**
--algorithm LamportMutex {

   fifo network[Nodes, Nodes];
       
   define {
     Max(c,d) == IF c > d THEN c ELSE d
     \* messages used in the algorithm
     Request(c) == [type |-> "request", clock |-> c]
     Release(c) == [type |-> "release", clock |-> c]
     Acknowledge(c) == [type |-> "ack", clock |-> c]
   }
     
   process(n \in Nodes)
     variables clock = 0,
               req = [n \in Nodes |-> 0],
               ack = {},
               sndr, msg;
   {
      
     p0: while (TRUE) {
         p1:   skip;  \* non-critical section
         p2:   clock := clock + 1;

               \*sender is the specific node, receivers are all other nodes
               multicast(network, [self, nd \in Nodes |-> Request(clock)]);
               req[self] := clock;
               ack := {self};
               
         p3:   await (/\ ack = Nodes
                      /\ \A n \in Nodes \ {self} : \/ req[n] = 0
                                                   \/ req[self] < req[n]
                                                   \/ (self < n /\ req[self] = req[n]));

         cs:   skip;
         p4:   clock := clock + 1;
               multicast(network, [self, n \in Nodes \ {self} |-> Release(clock)]);
               
               \*to be used on the entire channel not sub-parts
               \* clear(network); \* if we want to add this add -label to the options
       } \* end while
   }{

rcv:
     while (TRUE) {
        with (n \in Nodes) {
           sndr := n;
           receive(network[n,self], msg);
           clock := Max(clock, msg.clock) + 1
        };
handle:
        if (msg.type = "request") {
           req[sndr] := msg.clock;
           
           send(network[self, sndr], Acknowledge(clock))
        }
        else if (msg.type = "ack") {
           ack := ack \cup {sndr};
        }
        else if (msg.type = "release") {
           req[sndr] := 0;
        }
     }  \* end while
   } 
}
**)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-24c3ef96093575f8b57def32df87920b
CONSTANT defaultInitValue
VARIABLES network, pc

(* define statement *)
Max(c,d) == IF c > d THEN c ELSE d

Request(c) == [type |-> "request", clock |-> c]
Release(c) == [type |-> "release", clock |-> c]
Acknowledge(c) == [type |-> "ack", clock |-> c]

VARIABLES clock, req, ack, sndr, msg

vars == << network, pc, clock, req, ack, sndr, msg >>

NodeSet == (Nodes)

ThreadSet == [n \in NodeSet |-> 1..2]

Init == (* Global variables *)
        /\ network = [n0 \in Nodes, n1 \in Nodes |-> <<>>]
        (* Node n *)
        /\ clock = [self \in Nodes |-> 0]
        /\ req = [self \in Nodes |-> [n \in Nodes |-> 0]]
        /\ ack = [self \in Nodes |-> {}]
        /\ sndr = [self \in Nodes |-> defaultInitValue]
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in NodeSet |-> <<"p0","rcv">>]

p0(self) == /\ pc[self] [1] = "p0"
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "p1"]]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

p1(self) == /\ pc[self] [1] = "p1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "p2"]]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

p2(self) == /\ pc[self] [1] = "p2"
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ network' = [<<slf, nd>> \in DOMAIN network |->  IF slf = self 
                           /\ nd \in Nodes THEN 
                           Append(network[slf, nd], Request(clock'[self])) ELSE network[slf, nd]]
            /\ req' = [req EXCEPT ![self][self] = clock'[self]]
            /\ ack' = [ack EXCEPT ![self] = {self}]
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "p3"]]
            /\ UNCHANGED << sndr, msg >>

p3(self) == /\ pc[self] [1] = "p3"
            /\ (/\ ack[self] = Nodes
                /\ \A n \in Nodes \ {self} : \/ req[self][n] = 0
                                             \/ req[self][self] < req[self][n]
                                             \/ (self < n /\ req[self][self] = req[self][n]))
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "cs"]]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

cs(self) == /\ pc[self] [1] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "p4"]]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

p4(self) == /\ pc[self] [1] = "p4"
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ network' = [<<slf, n>> \in DOMAIN network |->  IF slf = self 
                           /\ n \in Nodes \ { self } THEN 
                           Append(network[slf, n], Release(clock'[self])) ELSE network[slf, n]]
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "p0"]]
            /\ UNCHANGED << req, ack, sndr, msg >>

rcv(self) == /\ pc[self] [2] = "rcv"
             /\ \E n \in Nodes:
                  /\ sndr' = [sndr EXCEPT ![self] = n]
                  /\ Len(network[n,self]) > 0 
                  /\ msg' = [msg EXCEPT ![self] = Head(network[n,self])]
                  /\ network' = [network EXCEPT ![n,self] =  Tail(@) ]
                  /\ clock' = [clock EXCEPT ![self] = Max(clock[self], msg'[self].clock) + 1]
             /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![2] = "handle"]]
             /\ UNCHANGED << req, ack >>

handle(self) == /\ pc[self] [2] = "handle"
                /\ IF msg[self].type = "request"
                      THEN /\ req' = [req EXCEPT ![self][sndr[self]] = msg[self].clock]
                           /\ network' = [network EXCEPT ![self, sndr[self]] =  Append(@, Acknowledge(clock[self]))]
                           /\ ack' = ack
                      ELSE /\ IF msg[self].type = "ack"
                                 THEN /\ ack' = [ack EXCEPT ![self] = ack[self] \cup {sndr[self]}]
                                      /\ req' = req
                                 ELSE /\ IF msg[self].type = "release"
                                            THEN /\ req' = [req EXCEPT ![self][sndr[self]] = 0]
                                            ELSE /\ TRUE
                                                 /\ req' = req
                                      /\ ack' = ack
                           /\ UNCHANGED network
                /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![2] = "rcv"]]
                /\ UNCHANGED << clock, sndr, msg >>

n(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3(self) \/ cs(self)
              \/ p4(self) \/ rcv(self) \/ handle(self)

Next == (\E self \in Nodes: n(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-36a73cff8974d64609a72552526687d8

StateConstraint == 
  /\ \A x \in Nodes : clock[x] < 4
  /\ \A x,y \in Nodes : Len(network[x,y]) < 3
=============================================================================
