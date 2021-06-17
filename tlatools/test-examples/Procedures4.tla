------------------------ MODULE Procedures4 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

channel chan;

procedure f(msg) {
    Send:
        send(chan, msg);
        return;
}

procedure g() {
    Clear:
        clear(chan);
        return;
}

process (q \in Nodes)
{
    Act1:
        call g();
} {
    Act2:
        call f("msg");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-331333f3bb6a7e4cc2177c66bb6cafd9
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, msg

vars == << chan, pc, stack, msg >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = {}
        (* Procedure f *)
        /\ msg = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Act1","Act2">>]

Send(self, subprocess) == /\ pc[self][subprocess] = "Send"
                          /\ chan' = (chan \cup {msg[self][subprocess]})
                          /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                          /\ msg' = [msg EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).msg]
                          /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]

f(self, subprocess) == Send(self, subprocess)

Clear(self, subprocess) == /\ pc[self][subprocess] = "Clear"
                           /\ chan' = {}
                           /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                           /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                           /\ msg' = msg

g(self, subprocess) == Clear(self, subprocess)

Act1(self) == /\ pc[self][1]  = "Act1"
              /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "g",
                                                          pc        |->  "Done" ] >>
                                                      \o stack[self][1]]
              /\ pc' = [pc EXCEPT ![self][1] = "Clear"]
              /\ UNCHANGED << chan, msg >>

Act2(self) == /\ pc[self][2]  = "Act2"
              /\ /\ msg' = [msg EXCEPT ![self][2] = "msg"]
                 /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "f",
                                                             pc        |->  "Done",
                                                             msg       |->  msg[self][2] ] >>
                                                         \o stack[self][2]]
              /\ pc' = [pc EXCEPT ![self][2] = "Send"]
              /\ chan' = chan

q(self) == Act1(self) \/ Act2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess) \/ g(self, subprocess))
           \/ (\E self \in Nodes: q(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-51e35ce913548fccaa90cbc8be43e052


=========================================================
