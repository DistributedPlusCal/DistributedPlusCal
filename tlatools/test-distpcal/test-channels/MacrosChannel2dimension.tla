------------------------ MODULE MacrosChannel2dimensions -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> 0 ],  
          cur = 22;

channels ch2[Nodes][Nodes];
fifo fif2[Nodes][Nodes];

macro sendMacro(chanName, im) {
	send(chanName, im);
}
macro receiveMacro(chanName, rm) {
	receive(chanName, rm);
}

process ( pid \in Nodes )
variable c = 3, d = 1, e = 7;
{
	e := e+self;
    S2:
    send(ch2[2,2],e);
    send(fif2[2,2],e);
    SM2:
    e := e+30;
    sendMacro(ch2[2,2],e);
    sendMacro(fif2[2,2],e);
}
{
    R2:
    receive(ch2[2,2], cur);
    receive(fif2[2,2], cur);
    RM2:
    receiveMacro(ch2[2,2], cur);
    receiveMacro(fif2[2,2], cur);
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

