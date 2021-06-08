------------------------ MODULE Procedures3 -------------------------
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

process (q \in Nodes)
{
    Clear:
        clear(chan);
} {
    Sdr:
        call f("msg");
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ecf69795c6ab41933243d1a72119fc54
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, msg

vars == << chan, pc, stack, msg >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = {}
        (* Procedure f *)
        /\ msg = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Clear","Sdr">>]

Send(self, subprocess) == /\ pc[self][subprocess] = "Send"
                          /\ chan' = (chan \cup {msg[self][subprocess]})
                          /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                          /\ msg' = [msg EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).msg]
                          /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]

f(self, subprocess) == Send(self, subprocess)

Clear(self) == /\ pc[self] = "Clear"
               /\ chan' = {}
               /\ pc' = [pc EXCEPT ![self][1] = "Done"]
               /\ UNCHANGED << stack, msg >>

Sdr(self) == /\ pc[self] = "Sdr"
             /\ /\ msg' = [msg EXCEPT ![self] = "msg"]
                /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "f",
                                                            pc        |->  "Done",
                                                            msg       |->  msg[self][2] ] >>
                                                        \o stack[self][2]]
             /\ pc' = [pc EXCEPT ![self][2] = "Send"]
             /\ chan' = chan

q(self) ==  \/ Clear(self) \/ Sdr(self)

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ (\E self \in Nodes: q(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9b32fa7b23b697a568f359ab34da58a3


=========================================================
