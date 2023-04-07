------------------------ MODULE TwoProcessesGlobalChannel -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in (Nodes \cup {Id}) |-> ind ],  
          cur = "none";

channels ch[Nodes \cup {Id}], ch2[Nodes][Nodes];
fifo fi[Nodes \cup {Id}];

process ( pid \in Nodes )
variable c = 3;
{
    PL:
	c := c+1;
    S1:
    send(ch[Id], c+self);
    S2:
    send(ch[Id], ar[self]);
}

process ( qid = Id )
variable d = 4;
{
    R1:
	receive(ch[Id], d);
    R2:
	receive(ch[Id], ar[Id]);
    (* just to lock at the trace *)
    DeadLock:
    await d < 0;
}

}
*)
==========================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}

