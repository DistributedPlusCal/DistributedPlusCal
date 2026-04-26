------------------------ MODULE OneProcessMultiThreadMacroP  -------------------------
EXTENDS Naturals, TLC

CONSTANT N           (* Size of arrays *)
\* N == 2
CONSTANT MAXINT      (* Size of arrays *)
\* MAXINT == 3

(* PlusCal options (-label -termination -distpcal) *)

(*--algorithm Dummy 
variables 
    ar \in [ 1..N -> 0..MAXINT ],  (* Array of N integers in 0..MAXINT *)
    x \in 0..MAXINT,               
    i = 1;

macro mymacro(ind,newv)
begin
    ar[ind] := newv;
	ind := ind + 1;
end macro

process pid = 1
begin
    x := 1;
	mymacro(i,x);
end thread
begin
	mymacro(i,x);
    ar[i] := 0;
end thread

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a7588a5d" /\ chksum(tla) = "8a56199f")
VARIABLES pc, ar, x, i

vars == << pc, ar, x, i >>

ProcSet == {1}

SubProcSet == [self \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ ar \in [ 1..N -> 0..MAXINT ]
        /\ x \in 0..MAXINT
        /\ i = 1
        /\ pc = [self \in ProcSet |-> <<"Lbl_1","Lbl_2">>]

Lbl_1 == /\ pc[1][1]  = "Lbl_1"
         /\ x' = 1
         /\ ar' = [ar EXCEPT ![i] = x']
         /\ i' = i + 1
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

pid_thread_1 == Lbl_1

Lbl_2 == /\ pc[1][2]  = "Lbl_2"
         /\ ar' = [ar EXCEPT ![i] = x]
         /\ i' = i + 1
         /\ pc' = [pc EXCEPT ![1][2] = "Lbl_3"]
         /\ x' = x

Lbl_3 == /\ pc[1][2]  = "Lbl_3"
         /\ ar' = [ar EXCEPT ![i] = 0]
         /\ pc' = [pc EXCEPT ![1][2] = "Done"]
         /\ UNCHANGED << x, i >>

pid_thread_2 == Lbl_2 \/ Lbl_3

pid == pid_thread_1 \/ pid_thread_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A thread \in SubProcSet[self]: pc[self][thread] = "Done"
               /\ UNCHANGED vars

Next == pid
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(pid_thread_1)
        /\ WF_vars(pid_thread_2)

Termination == <>(\A self \in ProcSet: \A thread \in SubProcSet[self] : pc[self][thread] = "Done")

\* END TRANSLATION 
 
=============================================================================
{
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "N": 2,
        "MAXINT": 3
    },
    "compare_path": "compile",
    "compare_to": "test-one_process/OneProcessMultiThreadMacroC.tla"
}
