------------------------ MODULE SingleProcessSendC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

variable c = {};
\* channel chan;

process ( rm = 1 ) {
    Star1:
    c := c \union {1};
    \* send(chan, 2);
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-773d7b1eed01da395cf7136cf942bbf6
VARIABLES c, pc

vars == << c, pc >>

ProcSet == {1}

SubProcSet == [n \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ c = {}

Star1 == /\ pc[1] [1] = "Star1"
         /\ c' = (c \union {1})
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

rm ==  \/ Star1

Next == rm

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e563293126d0822866417d5f2339083c

==========================================================
