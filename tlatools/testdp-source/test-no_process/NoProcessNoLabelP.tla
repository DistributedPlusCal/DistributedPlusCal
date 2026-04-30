------------------------ MODULE NoProcessNoLabelP -------------------------
EXTENDS Naturals, TLC

(*--algorithm Dummy 
variables i = 1;
begin
    i := i + 1;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "caf5039d" /\ chksum(tla) = "f27f17f")
VARIABLES pc, i

vars == << pc, i >>

Init == (* Global variables *)
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ i' = i + 1
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {},
    "compare_path": "compile",
    "compare_to": "test-no_process/NoProcessNoLabelC.tla"
}
