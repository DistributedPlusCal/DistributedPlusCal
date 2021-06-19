------------------------ MODULE LogicalClock -------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

   fifos network[Nodes, Nodes];

   define {
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
                   receiveWithClock(network[n,self], msg, clock); sndr := n;
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
}  
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a4cecd991a6e503f409550e8c278a2d2
CONSTANT defaultInitValue
VARIABLES network, pc

(* define statement *)
beats(a,b) == \/ req[b] = 0
              \/ req[a] < req[b] \/ (req[a] = req[b] /\ a < b)

Request(c) == [type |-> "request", clock |-> c]
Release(c) == [type |-> "release", clock |-> c]
Acknowledge(c) == [type |-> "ack", clock |-> c]

VARIABLES req, ack, sndr, msg, clock

vars == << network, pc, req, ack, sndr, msg, clock >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]

(* Comparator for lamport clocks *)
Max(_c, _d) == IF _c > _d THEN _c ELSE _d

Init == (* Global variables *)
        /\ network = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        (* Process n *)
        /\ req = [self \in Nodes |-> [n \in Nodes |-> 0]]
        /\ ack = [self \in Nodes |-> {}]
        /\ sndr = [self \in Nodes |-> defaultInitValue]
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ clock = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> <<"ncs","rcv">>]

ncs(self) == /\ pc[self][1]  = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self][1] = "try"]
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ UNCHANGED << network, req, ack, sndr, msg >>

try(self) == /\ pc[self][1]  = "try"
             /\ req' = [req EXCEPT ![self][self] = clock[self]]
             /\ ack' = [ack EXCEPT ![self] = {self}]
             /\ network' = [_n0 \in Nodes, _n1 \in Nodes |->  Append(network[_n0, _n1] , [msg |-> "request", clock |-> clock])]
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
             /\ pc' = [pc EXCEPT ![self][1] = "enter"]
             /\ UNCHANGED << sndr, msg >>

enter(self) == /\ pc[self][1]  = "enter"
               /\ (ack[self] = Nodes /\ \A n \in Nodes \ {self} : beats(self, n))
               /\ pc' = [pc EXCEPT ![self][1] = "cs"]
               /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
               /\ UNCHANGED << network, req, ack, sndr, msg >>

cs(self) == /\ pc[self][1]  = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self][1] = "exit"]
            /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
            /\ UNCHANGED << network, req, ack, sndr, msg >>

exit(self) == /\ pc[self][1]  = "exit"
              /\ network' = [_n0 \in Nodes, _n1 \in Nodes |->  Append(network[_n0, _n1] , [msg |-> "release", clock |-> clock])]
              /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
              /\ pc' = [pc EXCEPT ![self][1] = "ncs"]
              /\ UNCHANGED << req, ack, sndr, msg >>

rcv(self) == /\ pc[self][2]  = "rcv"
             /\ \E n \in Nodes:
                  /\ Len(network[n,self]) > 0 
                  /\ msg' = [msg EXCEPT ![self] = Head(network[n,self])]
                  /\ network' = [network EXCEPT ![n,self] =  Tail(@) ]
                  /\ clock' = [clock EXCEPT ![self] = Max(clock[self], msg.clock) + 1]
                  /\ sndr' = [sndr EXCEPT ![self] = n]
             /\ pc' = [pc EXCEPT ![self][2] = "handle"]
             /\ UNCHANGED << req, ack >>

handle(self) == /\ pc[self][2]  = "handle"
                /\ IF msg[self].type = "request"
                      THEN /\ req' = [req EXCEPT ![self][sndr[self]] = msg[self].clock]
                           /\ network' = [network EXCEPT ![self, sndr[self]] =  Append(@, [msg |-> "ack", clock |-> clock])]
                           /\ clock' = [clock EXCEPT ![self] = clock[self] + 1 ]
                           /\ ack' = ack
                      ELSE /\ IF msg[self].type = "ack"
                                 THEN /\ ack' = [ack EXCEPT ![self] = ack[self] \cup {sndr[self]}]
                                      /\ req' = req
                                 ELSE /\ IF msg[self].type = "release"
                                            THEN /\ req' = [req EXCEPT ![self][sndr[self]] = 0]
                                            ELSE /\ TRUE
                                                 /\ req' = req
                                      /\ ack' = ack
                           /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
                           /\ UNCHANGED << network >>
                /\ pc' = [pc EXCEPT ![self][2] = "rcv"]
                /\ UNCHANGED << sndr, msg >>

n(self) == ncs(self) \/ try(self) \/ enter(self) \/ cs(self) \/ exit(self)
              \/ rcv(self) \/ handle(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: n(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2d3503b9e447e6ef4d10acc732c46c58



============================================================================================
