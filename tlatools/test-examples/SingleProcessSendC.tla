------------------------ MODULE SingleProcessSendC -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo {

variable c = {};
channel chan;

process ( rm = 1 ) {
    Star1:
    c := c \union {1};
    send(chan, 2);
}


}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4748aae827ae61b6944d346b35412970
VARIABLES c, chan, pc

vars == << c, chan, pc >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ c = {}
        /\ chan = {}
        /\ pc = [self \in ProcSet |-> <<"Star1">>]

Star1 == /\ pc[1][1]  = "Star1"
         /\ c' = (c \union {1})
         /\ chan' = (chan \cup {2})
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

rm == Star1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == rm
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-712552525a8d959ca056f5841d69c976

==========================================================
