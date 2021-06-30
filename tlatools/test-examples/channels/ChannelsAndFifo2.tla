------------------------ MODULE ChannelsAndFifo2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

channel chan[Nodes], f_chan; \* the problem is about declaring consecutively channels

{
    Add:
        send(f_chan, "msg");
} 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7bea03b1ede3051153bb20825c5d182e
VARIABLES chan, f_chan, pc

vars == << chan, f_chan, pc >>

Init == (* Global variables *)
        /\ chan = [_n420 \in Nodes |-> {}]
        /\ f_chan = {}
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ f_chan' = (f_chan \cup {"msg"})
       /\ pc' = "Done"
       /\ chan' = chan

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Add
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a273c684e837f4aa18bac600a3a11f11


=========================================================
