----------------------------- MODULE 2PhaseCommit -----------------------------
EXTENDS Sequences, Naturals

CONSTANTS Coord, Agent

State == {"unknown", "accept", "refuse", "commit", "abort"}

	
(* PlusCal options (-distpcal) *)

(***
--algorithm TwoPhaseCommit {
 
  \* message channels
  channels coord, agt[Agent];
   
  macro trigger() {
        if (aState = "unknown") {
            with(st \in {"accept", "refuse"}) {
                aState := st;
                send(coord, [type |-> st, agent |-> self]);
            };
        };
  }

  macro respond() {
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

  fair process (a \in Agent)
        variables aState = "unknown"; 
  {
        a1: 
            trigger();
        a2: 
            await(aState \in {"commit", "abort"})
    
  } {
        a3:
            await (aState # "unknown");
            receive(agt[self], aState); 
	    a4:
            clear(agt);
  }

  fair process (c = Coord) 
        variables cState = "unknown",
            commits = {}, msg = {}; \* agents that agree to commit
  {
        c1: 
            await(cState \in {"commit", "abort"});    
		    broadcast(agt, [ag \in Agent|-> cState]);
  } {
        
        c2:
            while (cState \notin {"abort", "commit"}) {
                respond();
            }   
  }

 }
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2579b7add9117748632be3490d2a8fc1
VARIABLES coord, agt, pc, aState, cState, commits, msg

vars == << coord, agt, pc, aState, cState, commits, msg >>

ProcSet == (Agent) \cup {Coord}

SubProcSet == [_n42 \in ProcSet |-> IF _n42 \in Agent THEN 1..2
                                   ELSE (**Coord**) 1..2]

Init == (* Global variables *)
        /\ coord = {}
        /\ agt = [_ma430 \in Agent |-> {}]
        (* Process a *)
        /\ aState = [self \in Agent |-> "unknown"]
        (* Process c *)
        /\ cState = "unknown"
        /\ commits = {}
        /\ msg = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Agent -> <<"a1","a3">>
                                        [] self = Coord -> <<"c1","c2">>]

a1(self) == /\ pc[self][1]  = "a1"
            /\ IF aState[self] = "unknown"
                  THEN /\ \E st \in {"accept", "refuse"}:
                            /\ aState' = [aState EXCEPT ![self] = st]
                            /\ coord' = (coord \cup {[type |-> st, agent |-> self]})
                  ELSE /\ TRUE
                       /\ UNCHANGED << coord, aState >>
            /\ pc' = [pc EXCEPT ![self][1] = "a2"]
            /\ UNCHANGED << agt, cState, commits, msg >>

a2(self) == /\ pc[self][1]  = "a2"
            /\ (aState[self] \in {"commit", "abort"})
            /\ pc' = [pc EXCEPT ![self][1] = "Done"]
            /\ UNCHANGED << coord, agt, aState, cState, commits, msg >>

a3(self) == /\ pc[self][2]  = "a3"
            /\ (aState[self] # "unknown")
            /\ \E _a1519 \in agt[self]:
                 /\ aState' = [aState EXCEPT ![self] = _a1519]
                 /\ agt' = [agt EXCEPT ![self] = agt[self] \ {_a1519}]
            /\ pc' = [pc EXCEPT ![self][2] = "a4"]
            /\ UNCHANGED << coord, cState, commits, msg >>

a4(self) == /\ pc[self][2]  = "a4"
            /\ agt' = [_a0 \in Agent |-> {}]
            /\ pc' = [pc EXCEPT ![self][2] = "Done"]
            /\ UNCHANGED << coord, aState, cState, commits, msg >>

a(self) == a1(self) \/ a2(self) \/ a3(self) \/ a4(self)

c1 == /\ pc[Coord][1]  = "c1"
      /\ (cState \in {"commit", "abort"})
      /\ agt' = [_a0 \in Agent |-> agt[_a0] \cup {[ag \in Agent|-> cState]}]
      /\ pc' = [pc EXCEPT ![Coord][1] = "Done"]
      /\ UNCHANGED << coord, aState, cState, commits, msg >>

c2 == /\ pc[Coord][2]  = "c2"
      /\ IF cState \notin {"abort", "commit"}
            THEN /\ \E _c1512 \in coord:
                      /\ coord' = coord \ {_c1512}
                      /\ msg' = _c1512
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
                 /\ pc' = [pc EXCEPT ![Coord][2] = "c2"]
            ELSE /\ pc' = [pc EXCEPT ![Coord][2] = "Done"]
                 /\ UNCHANGED << coord, cState, commits, msg >>
      /\ UNCHANGED << agt, aState >>

c == c1 \/ c2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == c
           \/ (\E self \in Agent: a(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Agent : \A subprocess \in SubProcSet[self] : WF_vars(a(self))
        /\ WF_vars(c)

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-11c07083b69297c384a0af26b17fffa9


=============================================================================
