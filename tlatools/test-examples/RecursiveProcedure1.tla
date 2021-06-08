 ------------------------ MODULE RecursiveProcedure1 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
Nodes == 1..N

(* PlusCal options (-distpcal) *)
 
(***
--algorithm message_queue {

channel chan[Nodes]

procedure fact(i, n) {
    Start:
    if ( n = 0 ) {
        send(chan[i], res);
        return;
    }
    else {
        res := res * ( n-1 );
        call fact(i, n-1);
    };
    End: return;
}

process ( w \in Nodes )
variables res = 1, val \in 3..8;
{
    Result:
        print res;
} {
    Read:
        call fact(self, val);
}

}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1cdaf4d5b08ab18d04c3f469557d9d20
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, i, n, res, val

vars == << chan, pc, stack, i, n, res, val >>

ProcSet == (Nodes)

SubProcSet == [_n \in ProcSet |-> 1..2]


Init == (* Global variables *)
        /\ chan = [_n0 \in Nodes |-> {}]
        (* Procedure fact *)
        /\ i = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ n = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Process w *)
        /\ res = [self \in Nodes |-> 1]
        /\ val \in [Nodes -> 3..8]
        /\ stack = [self \in ProcSet |-> << <<>> , <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Result","Read">>]

Start(self, subprocess) == /\ pc[self][subprocess] = "Start"
                           /\ IF n[self][subprocess] = 0
                                 THEN /\ chan' = [chan EXCEPT ![i[self][subprocess]] = chan[i[self][subprocess]] \cup {res[self][subprocess]}]
                                      /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                                      /\ i' = [i EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).i]
                                      /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                                      /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                                      /\ res' = res
                                 ELSE /\ res' = [res EXCEPT ![self][subprocess] = res[self][subprocess] * ( n[self][subprocess]-1 )]
                                      /\ /\ i' = [i EXCEPT ![self][subprocess] = i[self][subprocess]]
                                         /\ n' = [n EXCEPT ![self][subprocess] = n[self][subprocess]-1]
                                         /\ stack' = [stack EXCEPT ![self][subprocess] = << [ procedure |->  "fact",
                                                                                              pc        |->  "End",
                                                                                              i         |->  i[self][subprocess],
                                                                                              n         |->  n[self][subprocess] ] >>
                                                                                          \o stack[self][subprocess]]
                                      /\ pc' = [pc EXCEPT ![self][subprocess] = "Start"]
                                      /\ chan' = chan
                           /\ val' = val

End(self, subprocess) == /\ pc[self][subprocess] = "End"
                         /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                         /\ i' = [i EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).i]
                         /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                         /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                         /\ UNCHANGED << chan, res, val >>

fact(self, subprocess) == Start(self, subprocess) \/ End(self, subprocess)

Result(self) == /\ pc[self] = "Result"
                /\ PrintT(res[self])
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << chan, stack, i, n, res, val >>

Read(self) == /\ pc[self] = "Read"
              /\ /\ i' = [i EXCEPT ![self] = self]
                 /\ n' = [n EXCEPT ![self] = val[self]]
                 /\ stack' = [stack EXCEPT ![self][2] = << [ procedure |->  "fact",
                                                             pc        |->  "Done",
                                                             i         |->  i[self][2],
                                                             n         |->  n[self][2] ] >>
                                                         \o stack[self][2]]
              /\ pc' = [pc EXCEPT ![self][2] = "Start"]
              /\ UNCHANGED << chan, res, val >>

w(self) ==  \/ Result(self) \/ Read(self)

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  fact(self, subprocess))
           \/ (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0e66c765ab0c6598b7b1057b201edcb0



=============================================================================
