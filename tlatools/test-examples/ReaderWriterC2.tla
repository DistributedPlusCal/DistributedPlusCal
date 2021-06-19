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

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ queue = {}
        (* Procedure send_to *)
        /\ msg = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Write">>]

Sending(self, subprocess) == /\ pc[self][subprocess] = "Sending"
                             /\ queue' = (queue \cup {msg[self][subprocess]})
                             /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                             /\ msg' = [msg EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).msg]
                             /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]

send_to(self, subprocess) == Sending(self, subprocess)

Write == /\ pc[Writer][1]  = "Write"
         /\ /\ msg' = [msg EXCEPT ![Writer][1] = "msg"]
            /\ stack' = [stack EXCEPT ![Writer][1] = << [ procedure |->  "send_to",
                                                          pc        |->  "Done",
                                                          msg       |->  msg[Writer][1] ] >>
                                                      \o stack[Writer][1]]
         /\ pc' = [pc EXCEPT ![Writer][1] = "Sending"]
         /\ queue' = queue

w == Write

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == w
           \/ (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  send_to(self, subprocess))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3b0065f88572c2db517d4ce34a5b9b28


=============================================================================
