------------------------ MODULE NProcessesNoLabelNoPcP -------------------------
EXTENDS Naturals, TLC

(* PlusCal options (-label ) *)

(*--algorithm Dummy     
    variables i = 1;
    process pid \in 1..2
    begin
        while TRUE do
            i := i + 1;
        end while;
    end thread

    process qid \in 3..4
    begin
        while TRUE do
            i := i + 3;
        end while;
    end thread

    process sid = 5
    begin
        while TRUE do
            i := i + 5;
        end while;
    end thread
end algorithm

*)
\* BEGIN TRANSLATION (chksum(pcal) = "8a485af4" /\ chksum(tla) = "819845d6")
VARIABLE i

vars == << i >>

ProcSet == (1..2) \cup (3..4) \cup {5}

SubProcSet == [self \in ProcSet |->  CASE self \in 1..2 -> 1..1
                                     []   self \in 3..4 -> 1..1
                                     []   self = 5 -> 1..1 ]

Init == (* Global variables *)
        /\ i = 1

pid_thread_1(self) == i' = i + 1

pid(self) == pid_thread_1(self)

qid_thread_1(self) == i' = i + 3

qid(self) == qid_thread_1(self)

sid_thread_1 == i' = i + 5

sid == sid_thread_1

Next == sid
           \/ (\E self \in 1..2: pid(self))
           \/ (\E self \in 3..4: qid(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
{
    "need-error-parse": false,
    "just-sanity": true,
    "need-error-check": false,
    "model-checking-args": {},
	"compare_path": "compile",		
    "compare_to": "test-multiple_processes/NProcessesNoLabelNoPcC.tla"
}
