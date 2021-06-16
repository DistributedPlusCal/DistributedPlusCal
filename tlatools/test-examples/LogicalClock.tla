------------------------ MODULE LogicalClock -------------------------
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
     variables req = [n \in Nodes |-> 0],
               ack = {}, sndr, msg;
     lamportClock clock; \* declaring a logical lamport clock. 
   { \* thread executing the main algorithm
        ncs: 
            while (TRUE) {
               skip;  \* non-critical section
               try:   
                    req[self] := clock; 
                    ack := {self};
                    broadcastWithClock(network, "request", clock);
               enter: await (ack = Nodes /\ \A n \in Nodes \ {self} : beats(self, n));
        cs:    skip;  \* critical section
        exit:  broadcastWithClock(network, "release", clock);
     } \* end while
  }  { \* message handling thread
        rcv:   
            while (TRUE) { 
                with (n \in Nodes) {
                   receive(network[n,self], msg); sndr := n;
                };
                handle: 
                    if (msg.type = "request") {
                        req[sndr] := msg.clock;
                        sendWithClock(network[self, sndr], "ack", clock)
                    }
                    else if (msg.type = "ack") { 
                        ack := ack \cup {sndr}; 
                    }
                    else if (msg.type = "release") { 
                        req[sndr] := 0; 
                    }
             }  \* end while
   } \* end message handling thread
}  **)

\* THE TRANSLATION. LOGICAL CLOCKS
CONSTANT defaultInitValue
VARIABLES network, pc

(* define statement *)
Max(c,d) == IF c > d THEN c ELSE d
beats(a,b) == \/ req[b] = 0
              \/ req[a] < req[b] \/ (req[a] = req[b] /\ a < b)

Request(c) == [type |-> "request", clock |-> c]
Release(c) == [type |-> "release", clock |-> c]
Acknowledge(c) == [type |-> "ack", clock |-> c]

VARIABLES clock, req, ack, sndr, msg, _previous_clockValue \* for accessing the clock value in the message received

vars == << network, pc, clock, req, ack, sndr, msg, _previous_clockValue >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ network = [_n0 \in Nodes, _n1 \in Nodes |-> <<>>]
        (* Process n *)
        /\ clock = [self \in Nodes |-> 0]
        /\ req = [self \in Nodes |-> [n \in Nodes |-> 0]]
        /\ ack = [self \in Nodes |-> {}]
        /\ sndr = [self \in Nodes |-> defaultInitValue]
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> <<"ncs","rcv">>]
        (* The global variables appended for logical clocks *)
        /\ _previous_clockValue = 0

ncs(self) == /\ pc[self] [1] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "try"]
             /\ UNCHANGED << network, clock, req, ack, sndr, msg, _previous_clockValue >>

try(self) == /\ pc[self] [1] = "try"
                (* clock' is appended by the translator for all action labels once logical clocks are declared *)
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ req' = [req EXCEPT ![self][self] = clock'[self]]
             /\ ack' = [ack EXCEPT ![self] = {self}]
             (* broadcastWithCLock *)
             /\ network' = [network EXCEPT ![self] =
                               [dst \in Nodes |->
                                   IF dst = self THEN network[self][self]
                                         ELSE Append(network[self][dst], [type |-> "request", clock |-> clock'[self]])]]
             /\ pc' = [pc EXCEPT ![self][1] = "enter"]
             /\ UNCHANGED << sndr, msg, _previous_clockValue >>

enter(self) == /\ pc[self] [1] = "enter"
               /\ (ack[self] = Nodes /\ \A n \in Nodes \ {self} : beats(self, n))
               /\ pc' = [pc EXCEPT ![self][1] = "cs"]
                (* clock' is appended by the translator for all action labels once logical clocks are declared *)
               /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
               /\ UNCHANGED << network, req, ack, sndr, msg, _previous_clockValue >>
\* clock increase call is appened to "enter" label because for all action labels we add clock increase calls.

cs(self) == /\ pc[self] [1] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "exit"]
            /\ UNCHANGED << network, clock, req, ack, sndr, msg, _previous_clockValue >>

exit(self) == /\ pc[self] [1] = "exit"
                (* clock' is appended by the translator for all action labels once logical clocks are declared *)
              /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
              /\ network' = [<<slf, n>> \in DOMAIN network |->  IF slf = self 
                             /\ n \in Nodes \ { self } THEN 
                             Append(network[slf, n], [type |-> "release", clock |-> clock'[self]]) ELSE network[slf, n]]
              /\ pc' = [pc EXCEPT ![self][1] = "ncs"]
              /\ UNCHANGED << req, ack, sndr, msg, _previous_clockValue >>

rcv(self) == /\ pc[self] [2] = "rcv"
             /\ \E n \in Nodes:
                  /\ Len(network[n,self]) > 0 
                  /\ msg' = [msg EXCEPT ![self] = Head(network[n,self])]
                  /\ network' = [network EXCEPT ![n,self] =  Tail(@) ]
                  /\ sndr' = [sndr EXCEPT ![self] = n]
                  (* clock' is appended by the translator for all action labels once logical clocks are declared *)
                  /\ clock' = [clock EXCEPT ![self] = Max(clock[self], msg'[self].clock) + 1]
                  /\ _previous_clockValue' = msg'[self].clock;
             /\ pc' = [pc EXCEPT ![self][2] = "handle"]
             /\ UNCHANGED << req, ack>>

\*
*   Alternatively, clock' we can rewrite as follows
*   rcv(self) ==
*               /\ _previous_clockValue' = msg'[self].clock;
*               /\ clock' = [clock EXCEPT ![self] = Max(clock[self], _previous_clockValue) + 1]
*/

handle(self) == /\ pc[self] [2] = "handle"
                /\ IF msg[self].type = "request"
                      THEN /\ req' = [req EXCEPT ![self][sndr[self]] = msg[self].clock]
                           /\ network' = [network EXCEPT ![self, sndr[self]] =  Append(@, [type |-> "ack", clock |-> clock])]
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
                (* clock' is appended by the translator for all action labels once logical clocks are declared *)
                /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
                /\ UNCHANGED << clock, sndr, msg, _previous_clockValue >>

n(self) ==  \/ ncs(self) \/ try(self) \/ enter(self) \/ cs(self) \/ exit(self)
              \/ rcv(self) \/ handle(self)

Next == (\E self \in Nodes: n(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=======================