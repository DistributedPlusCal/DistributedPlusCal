------------------------ MODULE LamportMutex -------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N
(* PlusCal options (-distpcal) *)
(**--algorithm LamportMutex {
   fifos network[Nodes][Nodes];

   define {
     Max(c,d) == IF c > d THEN c ELSE d
     \* messages used in the algorithm
     Request(c) == [type |-> "request", clock |-> c]
     Release(c) == [type |-> "release", clock |-> c]
     Acknowledge(c) == [type |-> "ack", clock |-> c]
   }
   process(node \in Nodes)
     variables clock = 0, req = [n \in Nodes |-> 0],
               ack = {}, sndr = self, msg = Request(0);
   { \* thread executing the main algorithm
ncs: while (TRUE) {
       skip;  \* non-critical section
try:   clock := clock + 1; req[self] := clock; ack := {self};
       multicast(network, [m = self, n \in Nodes |-> Request(clock)]);
enter: await (ack = Nodes /\ \A n \in Nodes \ {self} : 
                                \/ req[n] = 0
                                \/ req[self] < req[n]
                                \/ req[self] = req[n] /\ self < n);
cs:    skip;  \* critical section
exit:  clock := clock + 1;
       multicast(network, [m = self, n \in Nodes \ {self} |-> Release(clock)]);
     } \* end while
  }  { \* message handling thread
rcv:   while (TRUE) { with (n \in Nodes) {
           receive(network[n,self], msg); sndr := n;
           clock := Max(clock, msg.clock) + 1
        };
handle: if (msg.type = "request") {
           req[sndr] := msg.clock;
           send(network[self,sndr], Acknowledge(clock))
        }
        else if (msg.type = "ack") { ack := ack \cup {sndr}; }
        else if (msg.type = "release") { req[sndr] := 0; };
        msg := Request(0);  \* reset to default values for reducing state space
        sndr := self;
     }  \* end while
   } \* end message handling thread
}  **)
\* BEGIN TRANSLATION (chksum(pcal) = "63255f1b" /\ chksum(tla) = "b3b0ed12")
VARIABLES network, pc

(* define statement *)
Max(c,d) == IF c > d THEN c ELSE d

Request(c) == [type |-> "request", clock |-> c]
Release(c) == [type |-> "release", clock |-> c]
Acknowledge(c) == [type |-> "ack", clock |-> c]

VARIABLES clock, req, ack, sndr, msg

vars == << network, pc, clock, req, ack, sndr, msg >>

ProcSet == (Nodes)

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ network = [_n20 \in  Nodes, _n31 \in  Nodes |-> <<>>]
        (* Process node *)
        /\ clock = [self \in Nodes |-> 0]
        /\ req = [self \in Nodes |-> [n \in Nodes |-> 0]]
        /\ ack = [self \in Nodes |-> {}]
        /\ sndr = [self \in Nodes |-> self]
        /\ msg = [self \in Nodes |-> Request(0)]
        /\ pc = [self \in ProcSet |-> <<"ncs","rcv">>]

ncs(self) == /\ pc[self][1]  = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "try"]
             /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

try(self) == /\ pc[self][1]  = "try"
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ req' = [req EXCEPT ![self][self] = clock'[self]]
             /\ ack' = [ack EXCEPT ![self] = {self}]
             /\ network' = [<<m,n>> \in DOMAIN network |->  IF m = self /\ n \in Nodes
                            THEN  Append(network[m,n], Request(clock'[self]))
                                   ELSE network[m,n]]
             /\ pc' = [pc EXCEPT ![self][1] = "enter"]
             /\ UNCHANGED << sndr, msg >>

enter(self) == /\ pc[self][1]  = "enter"
               /\ (ack[self] = Nodes /\ \A n \in Nodes \ {self} :
                                           \/ req[self][n] = 0
                                           \/ req[self][self] < req[self][n]
                                           \/ req[self][self] = req[self][n] /\ self < n)
               /\ pc' = [pc EXCEPT ![self][1] = "cs"]
               /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

cs(self) == /\ pc[self][1]  = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "exit"]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

exit(self) == /\ pc[self][1]  = "exit"
              /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
              /\ network' = [<<m,n>> \in DOMAIN network |->  IF m = self /\ n \in Nodes \ { self }
                             THEN  Append(network[m,n], Release(clock'[self]))
                                    ELSE network[m,n]]
              /\ pc' = [pc EXCEPT ![self][1] = "ncs"]
              /\ UNCHANGED << req, ack, sndr, msg >>

node1(self) == ncs(self) \/ try(self) \/ enter(self) \/ cs(self) \/ exit(self)

rcv(self) == /\ pc[self][2]  = "rcv"
             /\ \E n \in Nodes:
                  /\ Len(network[n,self]) > 0 
                  /\ msg' = [msg EXCEPT ![self] = Head(network[n,self])]
                  /\ network' = [network EXCEPT ![n,self] =  Tail(@) ]
                  /\ sndr' = [sndr EXCEPT ![self] = n]
                  /\ clock' = [clock EXCEPT ![self] = Max(clock[self], msg'[self].clock) + 1]
             /\ pc' = [pc EXCEPT ![self][2] = "handle"]
             /\ UNCHANGED << req, ack >>

handle(self) == /\ pc[self][2]  = "handle"
                /\ IF msg[self].type = "request"
                      THEN /\ req' = [req EXCEPT ![self][sndr[self]] = msg[self].clock]
                           /\ network' = [network EXCEPT ![self,sndr[self]] =  Append(@, Acknowledge(clock[self]))]
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
                /\ msg' = [msg EXCEPT ![self] = Request(0)]
                /\ sndr' = [sndr EXCEPT ![self] = self]
                /\ pc' = [pc EXCEPT ![self][2] = "rcv"]
                /\ clock' = clock

node2(self) == rcv(self) \/ handle(self)

node(self) == node1(self) \/ node2(self)

Next == (\E self \in Nodes: node(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Clock == Nat  \* override for finite-state model checking
Messages ==
    {Request(c) : c \in Clock} \union 
    {Acknowledge(c) : c \in Clock} \union 
    {Release(c) : c \in Clock}

TypeOK == 
    /\ req \in [Nodes -> [Nodes -> Clock]]
    /\ network \in [Nodes \X Nodes -> Seq(Messages)]
    /\ clock \in [Nodes -> Clock]
    /\ ack \in [Nodes -> SUBSET Nodes]
    /\ sndr \in [Nodes -> Nodes]
    /\ msg \in [Nodes -> Messages]

Mutex ==
    \A m,n \in Nodes: m # n => ~(pc[m] = "cs" /\ pc[n] = "cs")
=============================================================================
