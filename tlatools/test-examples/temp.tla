------------------------ MODULE temp -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm example {

variables chan = <<>>;

procedure f(x) {
    Add:
        chan := Append(chan, x);
        return;
}

process ( w \in Nodes )
variable cur = "none";
{
    rc:
        while (TRUE) {
            call f(cur);
        }
} 

}

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3118737da0f78fe2ad0dd64baca882b8
CONSTANT defaultInitValue
VARIABLES chan, pc, stack, x, cur

vars == << chan, pc, stack, x, cur >>

ProcSet == (Nodes)

SubProcSet == [_n42 \in ProcSet |-> 1..1]


Init == (* Global variables *)
        /\ chan = <<>>
        (* Procedure f *)
        /\ x = [ self \in ProcSet |-> [ subprocess \in SubProcSet[self] |-> defaultInitValue]]
        (* Process w *)
        /\ cur = [self \in Nodes |-> "none"]
        /\ stack = [self \in ProcSet |-> << <<>> >>]
                                      
        /\ pc = [self \in ProcSet |-> <<"rc">>]

Add(self, subprocess) == /\ pc[self][subprocess] = "Add"
                         /\ chan' = Append(chan, x[self][subprocess])
                         /\ pc' = [pc EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).pc]
                         /\ x' = [x EXCEPT ![self][subprocess] = Head(stack[self][subprocess]).x]
                         /\ stack' = [stack EXCEPT ![self][subprocess] = Tail(stack[self][subprocess])]
                         /\ cur' = cur

f(self, subprocess) == Add(self, subprocess)

rc(self) == /\ pc[self][1]  = "rc"
            /\ /\ stack' = [stack EXCEPT ![self][1] = << [ procedure |->  "f",
                                                           pc        |->  "rc",
                                                           x         |->  x[self][1] ] >>
                                                       \o stack[self][1]]
               /\ x' = [x EXCEPT ![self][1] = cur[self]]
            /\ pc' = [pc EXCEPT ![self][1] = "Add"]
            /\ UNCHANGED << chan, cur >>

w(self) == rc(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: \E subprocess \in SubProcSet[self] :  f(self, subprocess))
           \/ (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-05397bad3b3936cd529e65162f0efb7b


=========================================================
