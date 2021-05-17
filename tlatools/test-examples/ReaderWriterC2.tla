 ------------------------ MODULE ReaderWriterC2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Writer, Reader

(* PlusCal options (-distpcal) *)
 
(***
--algorithm message_queue {

channel queue;

procedure send_to(msg) {
    Sending:
      send(queue, msg);
      return;
}

process ( w = Writer )
{
	Write:
      call send_to("msg");
}

}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9feca28b47ce1a24e252b6a9395fbda7
CONSTANT defaultInitValue
VARIABLES queue, pc, stack, msg

vars == << queue, pc, stack, msg >>

ProcSet == {Writer}

SubProcSet == [n \in ProcSet |-> 1]

Sending(self, subprocess) == /\ pc[self][subprocess] [1] = "Sending"
                             /\ queue' = (queue \cup {msg[self][subprocess]})
                             /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                             /\ msg' = [msg EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).msg]
                             /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]

send_to(self, subprocess) == Sending(self, subprocess)

Write == /\ pc[Writer] [1] = "Write"
         /\ /\ msg' = [msg EXCEPT ![Writer] = "msg"]
            /\ stack' = [stack EXCEPT ![Writer][1] = << [ procedure |->  "send_to",
                                                          pc        |->  "Done",
                                                          msg       |->  msg[self][1] ] >>
                                                      \o stack[self][1]]
         /\ pc' = [pc EXCEPT ![Writer][1] = "Sending"]
         /\ queue' = queue

w ==  \/ Write

Next == w
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  send_to(self, subprocess))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-fdfaf86ce901fe1b5d177d0fb3dded58


=============================================================================
