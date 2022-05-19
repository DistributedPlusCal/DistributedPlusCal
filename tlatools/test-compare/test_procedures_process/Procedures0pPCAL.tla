------------------------ MODULE Procedures0p -------------------------
EXTENDS TLC, Integers, Sequences

(*
--algorithm Dummy {
variable c = 0, lp = 10, res = 1;

procedure f(x)
variable lv = 0;
{
    Add:
        c := x + 1;
				lv := lv + 2;
				x := lv + 3;
		End:
        return;
}

{
   Before:
	      lp := lp + 1;
   Sdr:
        call f(lp);
	 After:
	      res := lp;
} 

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7412a5d7" /\ chksum(tla) = "53332d61")
CONSTANT defaultInitValue
VARIABLES c, lp, res, pc, stack, x, lv

vars == << c, lp, res, pc, stack, x, lv >>

Init == (* Global variables *)
        /\ c = 0
        /\ lp = 10
        /\ res = 1
        (* Procedure f *)
        /\ x = defaultInitValue
        /\ lv = 0
        /\ stack = << >>
        /\ pc = "Before"

Add == /\ pc = "Add"
       /\ c' = x + 1
       /\ lv' = lv + 2
       /\ x' = lv' + 3
       /\ pc' = "End"
       /\ UNCHANGED << lp, res, stack >>

End == /\ pc = "End"
       /\ pc' = Head(stack).pc
       /\ lv' = Head(stack).lv
       /\ x' = Head(stack).x
       /\ stack' = Tail(stack)
       /\ UNCHANGED << c, lp, res >>

f == Add \/ End

Before == /\ pc = "Before"
          /\ lp' = lp + 1
          /\ pc' = "Sdr"
          /\ UNCHANGED << c, res, stack, x, lv >>

Sdr == /\ pc = "Sdr"
       /\ /\ stack' = << [ procedure |->  "f",
                           pc        |->  "After",
                           lv        |->  lv,
                           x         |->  x ] >>
                       \o stack
          /\ x' = lp
       /\ lv' = 0
       /\ pc' = "Add"
       /\ UNCHANGED << c, lp, res >>

After == /\ pc = "After"
         /\ res' = lp
         /\ pc' = "Done"
         /\ UNCHANGED << c, lp, stack, x, lv >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == f \/ Before \/ Sdr \/ After
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
		}
}
