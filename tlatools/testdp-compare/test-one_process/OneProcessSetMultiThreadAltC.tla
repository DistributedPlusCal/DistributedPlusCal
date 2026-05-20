------------------------ MODULE OneProcessSetMultiThreadAltC -------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT Nodes

(*--algorithm dummy 

variables i = 1;

process w \in Nodes 
variables l = 2;
begin
	Write:
  	while ( i < 4 ) do
        i := i+1;
		l := l+2;
  	end while
end thread
begin
	Read:
  	while ( l < 10 ) do
        i := i+1;
		l := l+2;    	    
  	end while
end thread

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "71b4d0d1" /\ chksum(tla) = "8d3134ca")
VARIABLES pc, i, l

vars == << pc, i, l >>

ProcSet == (Nodes)

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ i = 1
        (* Process w *)
        /\ l = [self \in Nodes |-> 2]
        /\ pc = [self \in ProcSet |-> <<"Write","Read">>]

Write(self) == /\ pc[self][1]  = "Write"
               /\ IF ( i < 4 )
                     THEN /\ i' = i+1
                          /\ l' = [l EXCEPT ![self] = l[self]+2]
                          /\ pc' = [pc EXCEPT ![self][1] = "Write"]
                     ELSE /\ pc' = [pc EXCEPT ![self][1] = "Done"]
                          /\ UNCHANGED << i, l >>

w_thread_1(self) == Write(self)

Read(self) == /\ pc[self][2]  = "Read"
              /\ IF ( l[self] < 10 )
                    THEN /\ i' = i+1
                         /\ l' = [l EXCEPT ![self] = l[self]+2]
                         /\ pc' = [pc EXCEPT ![self][2] = "Read"]
                    ELSE /\ pc' = [pc EXCEPT ![self][2] = "Done"]
                         /\ UNCHANGED << i, l >>

w_thread_2(self) == Read(self)

w(self) == w_thread_1(self) \/ w_thread_2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: w(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
=============================================================================
{
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "Nodes": "1..3"
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessSetMultiThreadP.tla"
}
