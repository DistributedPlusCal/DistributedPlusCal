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

{
    Add:
        send(network, "msg");
} 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7d049fd57fc2c3dad925f2f60daac2bf
VARIABLES x, chan, network, f_chan, t, pc

vars == << x, chan, network, f_chan, t, pc >>

Init == (* Global variables *)
        /\ x = 1
        /\ chan = [_n420 \in Nodes |-> {}]
        /\ network = {}
        /\ f_chan = <<>>
        /\ t = [_n430 \in Nodes, _n441 \in Nodes |-> <<>>]
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ network' = (network \cup {"msg"})
       /\ pc' = "Done"
       /\ UNCHANGED << x, chan, f_chan, t >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Add
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-212efad7a8fd57d81c2d062547cea856


=========================================================
