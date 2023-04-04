------------------------ MODULE OneProcessesThreadsMacrosChannels -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> ind ],  
          arr = [ ind \in Nodes |-> ar ],  
          cur = 22;

channels ch1[Nodes \cup {Id}];

macro sendMacro(chanName, im) {
	send(chanName, im);
}
macro sendMacroDim(chanName, im, n) {
	send(chanName[n], im);
}
macro receiveMacro(chanName, rm) {
	receive(chanName, rm[1]);
}
macro receiveMacroDim(chanName, rm, n) {
	receive(chanName[n], rm);
}

process ( pid \in Nodes )
variable c = 3, d = 1, e = 7;
{
	d := d+self;
    S1:
    send(ch1[1],d);
    SM1:
    d := d+40;
    sendMacro(ch1[1],ar[1]+40+self);
    SM2:
    d := d+80;
    sendMacroDim(ch1,d+self,1);
}
{
    R1:
    receive(ch1[1], cur);
    RM1:
    receiveMacro(ch1[1], arr[2]);
    RM2:
    receiveMacroDim(ch1, cur, 1);
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

