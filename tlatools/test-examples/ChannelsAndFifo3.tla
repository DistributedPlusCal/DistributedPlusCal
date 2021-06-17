------------------------ MODULE ChannelsAndFifo3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {


process (c = 1)
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4a35ca0cd73c341b8103e0e27f990d9e
CONSTANT defaultInitValue
VARIABLES pc, x, chan, f_chan

vars == << pc, x, chan, f_chan >>

ProcSet == {1}

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Process c *)
        /\ x = defaultInitValue
        /\ chan = {}
        /\ f_chan = <<>>
        /\ pc = [self \in ProcSet |-> <<"Add">>]

Add == /\ pc[1][1]  = "Add"
       /\ f_chan' =  Append(f_chan, "msg")
       /\ pc' = [pc EXCEPT ![1][1] = "Done"]
       /\ UNCHANGED << x, chan >>

c == Add

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == c
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f92cd70370d77df08cd827f25acfb1d


=========================================================
