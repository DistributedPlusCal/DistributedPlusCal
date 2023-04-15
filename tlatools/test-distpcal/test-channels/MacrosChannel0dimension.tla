------------------------ MODULE MacrosChannel0dimension -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> 0 ],  
          cur = 22;

channels ch;
fifo fif;

macro sendMacro(chanName, im) {
	send(chanName, im);
}
macro receiveMacro(chanName, rm) {
	receive(chanName, rm);
}

process ( pid \in Nodes )
variable c = 3;
{
	c := c+self;
    S:
    send(ch, c);
    send(fif, c);
    SM:
    c := c+50;
    sendMacro(ch,c);
    sendMacro(fif,c);
}
{
    R:
    receive(ch, cur);
    receive(fif, cur);
    RM:
    receiveMacro(ch, cur);
    receiveMacro(fif, cur);
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

