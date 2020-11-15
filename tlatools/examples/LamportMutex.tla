------------------------ MODULE LamportMutex -------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N
(* PlusCal options (-distpcal) *)
(**--algorithm LamportMutex {
   fifos network[Nodes, Nodes];
   define {
     Max(c,d) == IF c > d THEN c ELSE d
     beats(a,b) == \/ req[b] = 0
                   \/ req[a] < req[b] \/ (req[a] = req[b] /\ a < b)
     \* messages used in the algorithm
     Request(c) == [type |-> "request", clock |-> c]
     Release(c) == [type |-> "release", clock |-> c]
     Acknowledge(c) == [type |-> "ack", clock |-> c]
   }
   process(n \in Nodes)
     variables clock = 0, req = [n \in Nodes |-> 0],
               ack = {}, sndr, msg;
   { \* thread executing the main algorithm
ncs: while (TRUE) {
       skip;  \* non-critical section
try:   clock := clock + 1; req[self] := clock; ack := {self};
       multicast(network, [self, nd \in Nodes |-> Request(clock)]);
enter: await (ack = Nodes /\ \A n \in Nodes \ {self} : beats(self, n));
cs:    skip;  \* critical section
exit:  clock := clock + 1;
       multicast(network, [self, n \in Nodes \ {self} |->  Release(clock)]);
     } \* end while
  }  { \* message handling thread
rcv:   while (TRUE) { with (n \in Nodes) {
           receive(network[n,self], msg); sndr := n;
           clock := Max(clock, msg.clock) + 1
        };
handle: if (msg.type = "request") {
           req[sndr] := msg.clock;
           send(network[self, sndr], Acknowledge(clock))
        }
        else if (msg.type = "ack") { ack := ack \cup {sndr}; }
        else if (msg.type = "release") { req[sndr] := 0; }
     }  \* end while
   } \* end message handling thread
}  **)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-58c261f739df0a3487219675206874a4
CONSTANT defaultInitValue
VARIABLES network, pc

VARIABLES clock, req, ack, sndr, msg

vars == << network, pc, clock, req, ack, sndr, msg >>

ProcSet == (Nodes)

SubProcSet == [n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ network = [n0 \in Nodes, n1 \in Nodes |-> <<>>]
        (* Node n *)
        /\ clock = [self \in Nodes |-> 0]
        /\ req = [self \in Nodes |-> [n \in Nodes |-> 0]]
        /\ ack = [self \in Nodes |-> {}]
        /\ sndr = [self \in Nodes |-> defaultInitValue]
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"ncs","rcv">>]

(* define statement *)
Max(c,d) == IF c > d THEN c ELSE d
beats(a,b) == \/ req[b] = 0
              \/ req[a] < req[b] \/ (req[a] = req[b] /\ a < b)

Request(c) == [type |-> "request", clock |-> c]
Release(c) == [type |-> "release", clock |-> c]
Acknowledge(c) == [type |-> "ack", clock |-> c]

ncs(self) == /\ pc[self] [1] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "try"]
             /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

try(self) == /\ pc[self] [1] = "try"
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ req' = [req EXCEPT ![self][self] = clock'[self]]
             /\ ack' = [ack EXCEPT ![self] = {self}]
             /\ network' = [<<slf, nd>> \in DOMAIN network |->  IF slf = self 
                            /\ nd \in Nodes THEN 
                            Append(network[slf, nd], Request(clock'[self])) ELSE network[slf, nd]]
             /\ pc' = [pc EXCEPT ![self][1] = "enter"]
             /\ UNCHANGED << sndr, msg >>

enter(self) == /\ pc[self] [1] = "enter"
               /\ (ack[self] = Nodes /\ \A n \in Nodes \ {self} : beats(self, n))
               /\ pc' = [pc EXCEPT ![self][1] = "cs"]
               /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

cs(self) == /\ pc[self] [1] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "exit"]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg >>

exit(self) == /\ pc[self] [1] = "exit"
              /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
              /\ network' = [<<slf, n>> \in DOMAIN network |->  IF slf = self 
                             /\ n \in Nodes \ { self } THEN 
                             Append(network[slf, n], Release(clock'[self])) ELSE network[slf, n]]
              /\ pc' = [pc EXCEPT ![self][1] = "ncs"]
              /\ UNCHANGED << req, ack, sndr, msg >>

rcv(self) == /\ pc[self] [2] = "rcv"
             /\ \E n \in Nodes:
                  /\ Len(network[n,self]) > 0 
                  /\ msg' = [msg EXCEPT ![self] = Head(network[n,self])]
                  /\ network' = [network EXCEPT ![n,self] =  Tail(@) ]
                  /\ sndr' = [sndr EXCEPT ![self] = n]
                  /\ clock' = [clock EXCEPT ![self] = Max(clock[self], msg'[self].clock) + 1]
             /\ pc' = [pc EXCEPT ![self][2] = "handle"]
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
                /\ pc' = [pc EXCEPT ![self][2] = "rcv"]
                /\ UNCHANGED << clock, sndr, msg >>

n(self) ==  \/ ncs(self) \/ try(self) \/ enter(self) \/ cs(self) \/ exit(self)
              \/ rcv(self) \/ handle(self)

Next == (\E self \in Nodes: n(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d44b5f7fa8de17dba79eb4bb2762c474
=======================
