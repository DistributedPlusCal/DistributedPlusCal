----------------------------- MODULE 2PhaseCommit -----------------------------
EXTENDS Sequences, Naturals

CONSTANTS Coord, Agent

State == {"unknown", "accept", "refuse", "commit", "abort"}

	
(* PlusCal options (-distpcal) *)

(***
--algorithm TPC {
 
  \* message channels
  channels coord, agt[Agent];
     
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
    
    a3:await (aState # "unknown");
       receive(agt[self], aState); 
	   
	a4:clear(agt);
  }

  fair process (c = Coord) 
  variables cState = "unknown",
            commits = {}, msg = {};
             \* agents that agree to commit
  {
    c1: await(cState \in {"commit", "abort"});    
		broadcast(agt, [ag \in Agent|-> cState]);
  } {
        
     c2:while (cState \notin {"abort", "commit"}) {
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


=============================================================================
