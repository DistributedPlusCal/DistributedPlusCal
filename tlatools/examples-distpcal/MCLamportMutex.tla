------------------------ MODULE MCLamportMutex -------------------------------
(****************************************************************************)
(* Version of LamportMutex suitable for model checking with TLC. The set    *)
(* of clock values is overridden to a finite set so that TLC can evaluate   *)
(* the definition of the set Messages.                                      *)
(****************************************************************************)
EXTENDS LamportMutex
CONSTANT MaxClock   \* highest clock value to be considered for model checking

\* override the operator Clock with MCClock in the configuration file
MCClock == 0 .. MaxClock

\* State constraint for model checking.
\* It's enough to bound the values of the `clock' variables: the other
\* clock values follow, and the sizes of message channels are bounded.
StateConstraint ==
  /\ \A n \in Nodes : clock[n] < MaxClock

==============================================================================
Model checking statistics
N=3, MaxClock=5: 1,710,559 states (371,122 distinct), 00:19 mins
N=3, MaxClock=6: 16,669795 states (3,833,219 distinct), 02:53 mins
N=3, MaxClock=7: 100,513,225 states (24,006,964 distinct), 16:49 mins
