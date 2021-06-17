------------------------ MODULE ChannelsAndFifo4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {


process (c = 1)
channel chan[Nodes], f_chan; \* the problem is about declaring consecutively channels and fifos.
{
    Add:
        send(f_chan, "msg");
} 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-db073a74abe7f7829bb90d0b07eb3e42
VARIABLES pc, chan, f_chan

vars == << pc, chan, f_chan >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Process c *)
        /\ chan = {}
        /\ f_chan = {}
        /\ pc = [self \in ProcSet |-> <<"Add">>]

Add == /\ pc[1][1]  = "Add"
       /\ f_chan' = (f_chan \cup {"msg"})
       /\ pc' = [pc EXCEPT ![1][1] = "Done"]
       /\ chan' = chan

c == Add

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == c
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1b36c13adb1593f2eb13afd38e9f01f5


=========================================================
