----------------------------- MODULE 2pc -----------------------------
EXTENDS Sequences, Naturals

CONSTANTS Coord, Agent

State == {"unknown", "accept", "refuse", "commit", "abort"}

	
(* PlusCal options (-distpcal, -label) *)

(***
--algorithm TPC {
 
  \* message channels
  channels coord,agt[Agent];
     
  fair process (a \in Agent)
  variable aState = "unknown"; {
a1: if (aState = "unknown") {
        with(st \in {"accept", "refuse"}) {
          aState := st;
          send(coord, [type |-> st, agent |-> self]);
        };
    };
    a2: await(aState \in {"commit", "abort"})
    
  } {
    
    await (aState # "unknown");
    
    \* asynchronous message reception
    receive(agt[self], aState); 
	clear(agt);
  }
  fair process (c = Coord) 
  variables cState = "unknown",
            commits = {}, msg = {};
             \* agents that agree to commit
  {
    c1: await(cState \in {"commit", "abort"});
    
    
    broadcast(agt, [ag \in Agent|-> cState]);
    \* multicast(agt, [ag \in Agent |-> cState])
  } {
        
        while (cState \notin {"abort", "commit"}) {
        receive(coord, msg);
            if (msg.type = "refuse") {
                cState := "abort";
            }
            else if (msg.type = "accept") {
                commits := commits \cup {msg.agent};
                 if (commits = Agent) {
                    cState := "commit";
                 }
              }
        }
  }
 }
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ab3a94ac41b59cab280fd5445644e423
VARIABLES coord, agt, pc, aState, cState, commits, msg

vars == << coord, agt, pc, aState, cState, commits, msg >>

NodeSet == (Agent) \cup {Coord}

ThreadSet == [n \in NodeSet |-> IF n \in Agent THEN 1..2
                             ELSE (**Coord**) 1..2]

Init == (* Global variables *)
        /\ coord = {}
        /\ agt = [a0 \in Agent |-> {}]
        (* Node a *)
        /\ aState = [self \in Agent |-> "unknown"]
        (* Node c *)
        /\ cState = "unknown"
        /\ commits = {}
        /\ msg = {}
        /\ pc = [self \in NodeSet |-> CASE self \in Agent -> <<"a1","Lbl_1">>
                                        [] self = Coord -> <<"c1","Lbl_3">>]

a1(self) == /\ pc[self] [1] = "a1"
            /\ IF aState[self] = "unknown"
                  THEN /\ \E st \in {"accept", "refuse"}:
                            /\ aState' = [aState EXCEPT ![self] = st]
                            /\ coord' = (coord \cup {[type |-> st, agent |-> self]})
                  ELSE /\ TRUE
                       /\ UNCHANGED << coord, aState >>
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "a2"]]
            /\ UNCHANGED << agt, cState, commits, msg >>

a2(self) == /\ pc[self] [1] = "a2"
            /\ (aState[self] \in {"commit", "abort"})
            /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![1] = "Done"]]
            /\ UNCHANGED << coord, agt, aState, cState, commits, msg >>

Lbl_1(self) == /\ pc[self] [2] = "Lbl_1"
               /\ (aState[self] # "unknown")
               /\ \E a1518 \in agt[self]:
                    /\ aState' = [aState EXCEPT ![self] = a1518]
                    /\ agt' = [agt EXCEPT ![self] = agt[self] \ {a1518}]
               /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![2] = "Lbl_2"]]
               /\ UNCHANGED << coord, cState, commits, msg >>

Lbl_2(self) == /\ pc[self] [2] = "Lbl_2"
               /\ agt' = [a0 \in Agent |-> {}]
               /\ pc' = [pc EXCEPT ![self] = [@  EXCEPT ![2] = "Done"]]
               /\ UNCHANGED << coord, aState, cState, commits, msg >>

a(self) == a1(self) \/ a2(self) \/ Lbl_1(self) \/ Lbl_2(self)

c1 == /\ pc[Coord] [1] = "c1"
      /\ (cState \in {"commit", "abort"})
      /\ agt' = [ag \in Agent |-> agt[ag] \cup  {cState} ]
      /\ pc' = [pc EXCEPT ![Coord] = [@  EXCEPT ![1] = "Done"]]
      /\ UNCHANGED << coord, aState, cState, commits, msg >>

Lbl_3 == /\ pc[Coord] [2] = "Lbl_3"
         /\ IF cState \notin {"abort", "commit"}
               THEN /\ \E c1512 \in coord:
                         /\ coord' = coord \ {c1512}
                         /\ msg' = c1512
                    /\ IF msg'.type = "refuse"
                          THEN /\ cState' = "abort"
                               /\ UNCHANGED commits
                          ELSE /\ IF msg'.type = "accept"
                                     THEN /\ commits' = (commits \cup {msg'.agent})
                                          /\ IF commits' = Agent
                                                THEN /\ cState' = "commit"
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED cState
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << cState, commits >>
                    /\ pc' = [pc EXCEPT ![Coord] = [@  EXCEPT ![2] = "Lbl_3"]]
               ELSE /\ pc' = [pc EXCEPT ![Coord] = [@  EXCEPT ![2] = "Done"]]
                    /\ UNCHANGED << coord, cState, commits, msg >>
         /\ UNCHANGED << agt, aState >>

c == c1 \/ Lbl_3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in NodeSet : \A thread \in ThreadSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == c
           \/ (\E self \in Agent: a(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Agent : WF_vars(a(self))
        /\ WF_vars(c)

Termination == <>(\A self \in NodeSet: \A thread \in ThreadSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-90aa8e9d424dca09c2a66ab927d80549

=============================================================================