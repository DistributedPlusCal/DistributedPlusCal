---------------------------- MODULE MCPaxos ----------------------------------
(****************************************************************************)
(* Version of Paxos suitable for model checking with TLC. In particular,    *)
(* the set of ballots is overridden to a finite set so that TLC can         *)
(* evaluate the predicate for choosing a value.                             *)
(****************************************************************************)
EXTENDS Paxos

CONSTANT
    MaxBallot    \* highest ballot number to be used

\* override the operator Ballots with MCBallots in the configuration file
MCBallots == (0 .. MaxBallot) \X Nodes

\* impose the following state constraint: the maximum ballot number is
\* constrained to be strictly smaller than MaxBallot because a "1a" message
\* using the next-higher ballot number may always be sent
StateConstraint ==
    /\ \A n \in Nodes : maxBal[n][1] < MaxBallot
    /\ \A n \in Nodes : BagCardinality(ch[n]) < 3

==============================================================================
Model checking statistics (2.3 GHZ Intel i7, 16GB RAM):

N=3, MaxBallot=2, Values={v1,v2}: 
     5,920,497 states (762,857 distinct), 1:29 minutes
N=3, MaxBallot=3, Values={v1,v2}:
     TLC crashed after 32:34 hours
     5,920,868,973 states (711,620,471 distinct), 
     31,899,008 left on queue (max queue size > 37M states)
