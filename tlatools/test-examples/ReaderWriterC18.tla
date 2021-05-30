 ------------------------ MODULE ReaderWriterC18 -------------------------
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
    Read:
        call fact(self, val);
    Result:
        print res;
}

}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-12132f2a3a7db87ac6770cca3da1f506
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, i, n, res, val

vars == << chan, pc, stack, i, n, res, val >>

ProcSet == (Nodes)

SubProcSet == [_dm_23 \in ProcSet |-> 1]

Init == (* Global variables *)
        /\ chan = [n0 \in Nodes |-> {}]
        (* Procedure fact *)
        /\ i = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ n = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Node w *)
        /\ res = [self \in Nodes |-> 1]
        /\ val \in [Nodes -> 3..8]
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Start(self, subprocess) == /\ pc[self][subprocess] = "Start"
                           /\ IF n[self][subprocess] = 0
                                 THEN /\ chan' = [chan EXCEPT ![i[self][subprocess]] = chan[i[self][subprocess]] \cup {res[self][subprocess]}]
                                      /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                                      /\ i' = [i EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).i]
                                      /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                                      /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                                      /\ res' = res
                                 ELSE /\ res' = [res EXCEPT ![self] = res[self] * ( n[self]-1 )]
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

Read(self) == /\ pc[self] [1] = "Read"
              /\ /\ i' = [i EXCEPT ![self] = self]
                 /\ n' = [n EXCEPT ![self] = val[self]]
                 /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "fact",
                                                             pc        |->  "Result",
                                                             i         |->  i[self][1],
                                                             n         |->  n[self][1] ] >>
                                                         \o stack[self][1]]
              /\ pc' = [pc EXCEPT ![self][1] = "Start"]
              /\ UNCHANGED << chan, res, val >>

Result(self) == /\ pc[self] [1] = "Result"
                /\ PrintT(res[self])
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << chan, stack, i, n, res, val >>

w(self) ==  \/ Read(self) \/ Result(self)

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  fact(self, subprocess))
           \/ (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9d769aee0213ca00ee40f93f3c35a1f5



=============================================================================
