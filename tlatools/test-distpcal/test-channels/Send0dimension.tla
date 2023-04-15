------------------------ MODULE Send0dimension -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal -setchannels) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> ind ],  
          cur = 22;

channels ch;

process ( pid \in Nodes )
variable c = 3;
{
	c := c+self;
    SL:
    send(ch, c);
    SG:
    send(ch, cur);
    SA:
    send(ch, ar[1]);
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

