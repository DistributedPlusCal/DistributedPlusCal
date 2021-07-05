------------------------ MODULE ChannelsAndFifo1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variable x = 1;
channel chan[Nodes], network;
fifo f_chan, t[Nodes, Nodes];
lamportClock clock;

{
    Add:
        send(network, "msg");
} 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-99c8be4494e5ab2e51fa2bd37b1267b5
VARIABLES x, chan, network, f_chan, t, clock, pc

vars == << x, chan, network, f_chan, t, clock, pc >>

Init == (* Global variables *)
        /\ x = 1
        /\ chan = [_n420 \in Nodes |-> {}]
        /\ network = {}
        /\ f_chan = <<>>
        /\ t = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        /\ clock = 0
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ network' = (network \cup {"msg"})
       /\ pc' = "Done"
       /\ UNCHANGED << x, chan, f_chan, t, clock >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Add
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0aa9f136e9b13354bffa8f9ffb17ca64


=========================================================
