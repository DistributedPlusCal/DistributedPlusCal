------------------------ MODULE TwoProcessesLocalChannel -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1 .. 2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm Dummy {
variable cur = "none";
channel chan[Nodes];

process ( w \in Nodes )
variable c = 3;
fifos fifs[Nodes];
{
	Lab:
	c := c+1;
	Snd:
    send(chan[Id], c);
    send(fifs[self], "msg");
	Rcv:
    receive(fifs[self], cur);
}

process ( v = Id )
variable d = 4;
channel ch[Nodes];
{
	RcvId:
	receive(chan[self], d);
	SndId:
    send(ch[self], "msg");
}

}
*)
==========================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {  }
}
