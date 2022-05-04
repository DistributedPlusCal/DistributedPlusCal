------------------------ MODULE Procedures3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {
fifo chan[Nodes];
procedure receive_from_channel(i) {
	Receive:
		send(chan[i], "msg");
		return;
}
process ( w \in Nodes )
variable cur = "none";
{
    Read:
      skip;
    call receive_from_channel(self);
}
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-517f79d43c0820362d6277f596157650
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, i, cur

vars == << chan, pc, stack, i, cur >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]

Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> <<>>]
        (* Procedure receive_from_channel *)
        /\ i = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Receive(self, subprocess) == /\ pc[self][subprocess] = "Receive"
                             /\ chan' = [chan EXCEPT ![i[self][subprocess]] =  Append(@, "msg")]
                             /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                             /\ i' = [i EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).i]
                             /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                             /\ cur' = cur

receive_from_channel(self, subprocess) == Receive(self, subprocess)

Read(self) == /\ pc[self][1]  = "Read"
              /\ TRUE
              /\ /\ i' = [i EXCEPT ![self][1] = self]
                 /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "receive_from_channel",
                                                             pc        |->  "Done",
                                                             i         |->  i[self][1] ] >>
                                                         \o stack[self][1]]
              /\ pc' = [pc EXCEPT ![self][1] = "Receive"]
              /\ UNCHANGED << chan, cur >>

w(self) == Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  receive_from_channel(self, subprocess))
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-674a440c9323d1c1528ee4b138d77d24
================================================
