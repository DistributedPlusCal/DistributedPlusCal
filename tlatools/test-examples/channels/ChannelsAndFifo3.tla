------------------------ MODULE ChannelsAndFifo3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {


process (c \in Nodes)
variables x;
channel chan[Nodes]; \* the problem is about declaring consecutively channels and fifos.
fifo f_chan;
{
    Add:
        send(f_chan, "msg");
} 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bdc2441e7fca7df99bb37479a515e185
CONSTANT defaultInitValue
VARIABLES pc, x, chan, f_chan

vars == << pc, x, chan, f_chan >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Process c *)
        /\ x = [self \in Nodes |-> defaultInitValue]
        /\ chan = [self \in Nodes |-> {}]
        /\ f_chan = [self \in Nodes |-> <<>>]
        /\ pc = [self \in ProcSet |-> <<"Add">>]

Add(self) == /\ pc[self][1]  = "Add"
             /\ f_chan' = [f_chan EXCEPT ![self] =  Append(f_chan, "msg")]
             /\ pc' = [pc EXCEPT ![self][1] = "Done"]
             /\ UNCHANGED << x, chan >>

c(self) == Add(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: c(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7b2d7004426b029a06b92ce098c9fbb7


=========================================================
