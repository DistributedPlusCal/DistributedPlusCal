 ------------------------ MODULE RecursiveProcedure2 -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
Nodes == 1..N

(* PlusCal options (-distpcal) *)
 
(***
--algorithm fibonachi {

channel chan[Nodes]

procedure fib(i, n) {
    Start:
    if ( n = 0 ) {
        send(chan[i], f1);
        return;
    }
    else if ( n = 1 ) {
        send(chan[i], f1);
        return;
    }
    else {
        f0 := f1;
        f1 := f0 + f1;
        call fib(i, n-1);
    }
}

process ( w \in Nodes )
variables f0 = 1, f1 = 1, val \in 0..8;
{
    Read:
        call fib(self, val);
    Result:
        print f1;
}

}
***)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b51c8e745dabd7e4e7c2368ce590b686
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, i, n, f0, f1, val

vars == << chan, pc, stack, i, n, f0, f1, val >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = [_n430 \in Nodes |-> {}]
        (* Procedure fib *)
        /\ i = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        /\ n = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Process w *)
        /\ f0 = [self \in Nodes |-> 1]
        /\ f1 = [self \in Nodes |-> 1]
        /\ val \in [Nodes -> 0..8]
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"Read">>]

Start(self, subprocess) == /\ pc[self][subprocess] = "Start"
                           /\ IF n[self][subprocess] = 0
                                 THEN /\ chan' = [chan EXCEPT ![i[self][subprocess]] = chan[i[self][subprocess]] \cup {f1[self]}]
                                      /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                                      /\ i' = [i EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).i]
                                      /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                                      /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                                      /\ UNCHANGED << f0, f1 >>
                                 ELSE /\ IF n[self][subprocess] = 1
                                            THEN /\ chan' = [chan EXCEPT ![i[self][subprocess]] = chan[i[self][subprocess]] \cup {f1[self]}]
                                                 /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                                                 /\ i' = [i EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).i]
                                                 /\ n' = [n EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).n]
                                                 /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                                                 /\ UNCHANGED << f0, f1 >>
                                            ELSE /\ f0' = [f0 EXCEPT ![self] = f1[self]]
                                                 /\ f1' = [f1 EXCEPT ![self] = f0'[self] + f1[self]]
                                                 /\ /\ i' = [i EXCEPT ![self][subprocess] = i[self][subprocess]]
                                                    /\ n' = [n EXCEPT ![self][subprocess] = n[self][subprocess]-1]
                                                    /\ stack' = [stack EXCEPT ![self][subprocess] = << [ procedure |->  "fib",
                                                                                                         pc        |->  "Error",
                                                                                                         i         |->  i[self][subprocess],
                                                                                                         n         |->  n[self][subprocess] ] >>
                                                                                                     \o stack[self][subprocess]]
                                                 /\ pc' = [pc EXCEPT ![self][subprocess] = "Start"]
                                                 /\ chan' = chan
                           /\ val' = val

fib(self, subprocess) == Start(self, subprocess)

Read(self) == /\ pc[self][1]  = "Read"
              /\ /\ i' = [i EXCEPT ![self][1] = self]
                 /\ n' = [n EXCEPT ![self][1] = val[self]]
                 /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "fib",
                                                             pc        |->  "Result",
                                                             i         |->  i[self][1],
                                                             n         |->  n[self][1] ] >>
                                                         \o stack[self][1]]
              /\ pc' = [pc EXCEPT ![self][1] = "Start"]
              /\ UNCHANGED << chan, f0, f1, val >>

Result(self) == /\ pc[self][1]  = "Result"
                /\ PrintT(f1[self])
                /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                /\ UNCHANGED << chan, stack, i, n, f0, f1, val >>

w(self) == Read(self) \/ Result(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  fib(self, subprocess))
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f31a559544c2ff45f51a0d8f5e330b72


=============================================================================