------------------------ MODULE OneProcessesThreadsMacrosChannelNdimension -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> 0 ],  
          cur = 22;

channels ch1[Nodes \cup {Id}], ch2[Nodes][Nodes];
fifo fif1[Nodes], fif2[Nodes][Nodes];

macro sendMacro(chanName, im) {
	send(chanName, im);
}
macro receiveMacro(chanName, rm) {
	receive(chanName, rm);
}

process ( pid \in Nodes )
variable c = 3, d = 1, e = 7;
{
	d := d+self;
    S1:
    send(ch1[1],d);
    send(fif1[1],d);
    SM1:
    d := d+40;
    sendMacro(ch1[1],d);
    sendMacro(fif1[1],d);
    R1:
    receive(ch1[1], cur);
    receive(fif1[1], cur);
    RM1:
    receiveMacro(ch1[1], cur);
    receiveMacro(fif1[1], cur);
}
{
	e := e+self;
    S2:
    send(ch2[2,2],e);
    send(fif2[2,2],e);
    SM2:
    e := e+30;
    sendMacro(ch2[2,2],e);
    sendMacro(fif2[2,2],e);
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

