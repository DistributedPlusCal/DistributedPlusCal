------------------------ MODULE ReaderWriterC3 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variable cur = "none";
fifo chan[Nodes];

procedure f() {
	Label12:
		clear(chan);
		return;
}

process ( w \in Nodes )
{
	Write:
         send(chan[self], "msg");
   	Clear:
  		call f();
} {
	Read:
  	while ( TRUE ) {
    	     receive(chan[self], cur);
  	}
}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7c58fa9170027c3aa768996231d093fd
VARIABLES cur, chan, pc, stack

vars == << cur, chan, pc, stack >>

ProcSet == (Nodes)

SubProcSet == [n \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = [_n0 \in Nodes |-> <<>>]
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Label12(self, subprocess) == /\ pc[self][subprocess] [1] = "Label12"
                             /\ chan' = [_n0 \in Nodes |-> <<>>]
                             /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                             /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                             /\ cur' = cur

f(self, subprocess) == Label12(self, subprocess)

Write(self) == /\ pc[self] [1] = "Write"
               /\ chan' = [chan EXCEPT ![self] =  Append(@, "msg")]
               /\ pc' = [pc EXCEPT ![self][1] = "Clear"]
               /\ UNCHANGED << cur, stack >>

Clear(self) == /\ pc[self] [1] = "Clear"
               /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                           pc        |->  "Done" ] >>
                                                       \o stack[self][1]]
               /\ pc' = [pc EXCEPT ![self][1] = "Label12"]
               /\ UNCHANGED << cur, chan >>

Read(self) == /\ pc[self] [2] = "Read"
              /\ Len(chan[self]) > 0 
              /\ cur' = Head(chan[self])
              /\ chan' = [chan EXCEPT ![self] =  Tail(@) ]
              /\ pc' = [pc EXCEPT ![self][2] = "Read"]
              /\ stack' = stack

w(self) ==  \/ Write(self) \/ Clear(self) \/ Read(self)

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f025b5b08188eb56d70a3ad3b789f4d

==========================================================
