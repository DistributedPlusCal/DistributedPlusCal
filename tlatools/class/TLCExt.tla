------------------------------- MODULE TLCExt -------------------------------

LOCAL INSTANCE TLC
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

-----------------------------------------------------------------------------

\* AssertEq(a, b) is logically equivalent to the expression 'a = b'. If a and b are not equal, 
\* however, AssertEq(a, b) will print out the values of 'a' and 'b'. If the two values are equal,
\* nothing will be printed.
AssertEq(a, b) == 
    IF a # b THEN
        /\ PrintT("Assertion failed")
        /\ PrintT(a)
        /\ PrintT(b)
        /\ a = b
    ELSE a = b


AssertError(err, exp) ==
    LET FailsEval(e) == CHOOSE b \in BOOLEAN : TRUE \* Expression failed to evaluate. 
        TLCError     == CHOOSE s \in STRING  : TRUE \* TLC error string.
    IN IF FailsEval(exp) THEN Assert(err = TLCError, TLCError) ELSE TRUE

-----------------------------------------------------------------------------
(* HERE BE DRAGONS! The operators below are experimental! *)

PickSuccessor(exp) ==
  (******************************************************************************)
  (* When set as an action constraint in the configuration file, interactively  *)
  (* pick successor states during state exploration, iff the expression exp     *)
  (* evaluates to FALSE.  To always pick successor states manually, use         *)
  (* PickSuccessor(FALSE). To pick successor states when the current prefix of  *)
  (* behaviors exceeds 22 states, use PickSuccessor(TLCGet("level") < 23).      *)
  (******************************************************************************)
  IF (exp)
  THEN TRUE
  ELSE CHOOSE bool \in BOOLEAN : TRUE 

Trace == 
  (******************************************************************************)
  (* The sequence of states (represented as a record whose DOMAIN is the set of *)
  (* a spec's variables) from an initial state to the current state.  In other  *)
  (* words, a prefix - of a behavior - ending with the current state.  A way to *)
  (* think about this operator is to see it as an implicit history variable     *)
  (* that does not have to be explicitly specified at the level of the spec.    *)
  (* Note that op is incompatible with TLC!RandomElement and Randomization (see *)
  (* tlc2.tool.TLCTrace.getTrace(LongVec)) and will cause TLC to crash.  This   *)
  (* technical limitation could be removed though.                              *)
  (*                                                                            *)
  (* Beware that this operator and TraceFrom below are O(n^2) in the number     *)
  (* of states that TLC has to generate.                                        *)
  (******************************************************************************)
  TRUE \* TODO

TraceFrom(state) ==
  TRUE \* TODO

=============================================================================
