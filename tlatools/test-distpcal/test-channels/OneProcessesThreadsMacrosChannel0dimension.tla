------------------------ MODULE OneProcessesThreadsMacrosChannel0dimension -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2
Id == 3

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ ind \in Nodes |-> 0 ],  
          cur = 22;

channels ch, ch1[Nodes \cup {Id}], ch2[Nodes][Nodes];

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
    SM:
    c := c+50;
    sendMacro(ch,c); 
}
{
    R:
    receive(ch, cur);
    RM:
    receiveMacro(ch, cur);
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

