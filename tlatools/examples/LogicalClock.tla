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



========================================