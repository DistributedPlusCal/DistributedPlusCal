------------------------ MODULE OneProcessThreadsChannels -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> ind ],  
          cur = 22;

channels ch, ch1[Nodes \cup {Id}];

process ( pid \in Nodes )
variable c = 3;
{
	c := c+self;
    SL:
    send(ch, c+self);
    SG:
    send(ch, cur+self+11);
    SA:
    send(ch, ar[1]+self);
}
{
    RL:
    receive(ch, c);
    RG:
    receive(ch, cur);
    RA:
    receive(ch, ar[2]);
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

