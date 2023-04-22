------------------------ MODULE GlobalChannelCLASH -------------------------
EXTENDS TLC, Integers, Sequences, Bags

Nodes == 1..2
Id == 3
Ex == 4

(* PlusCal options (-label -distpcal) *)

(*--algorithm message_queue {

variables ar = [ (Nodes \cup {Id}) -> 0..2 ],  
          cur = 5;

channels chan, ch[Nodes \cup {Id}];
fifo fif, fi[Nodes \cup {Id}];

process ( pid \in Nodes )
variable c = 3;
{
    PL:
	c := c+1;
    send(chan, c);
    send(ch[Id], c);
    send(fif, c);
    send(fi[Id], c);
    send(chan, cur);
    send(ch[Id], cur);
    send(fi[Id], cur);
}

process ( qid = Id )
variable c = 4;
{
    QL:
    c := c+1;
    Rc:
	receive(chan, c);
    R:
	receive(ch[Id], c);
    \* should use label, otherwise translation not correct (condition on size on separate label)
    Rf:
	receive(fif, c);
    \* should use label, otherwise translation not correct (condition on size on separate label)
    RF:
	receive(fi[Id], c);
    cur := c+3;
}

process ( sid = Ex )
variable c = 5;
{
    SL:
    c := c+1;
    R1:
	receive(ch[Id], cur);
    Rf1:
	receive(fif, cur);
    RF1:
	receive(fi[Id], cur);
}

process ( ssid = 7 )
variable c = 5;
{
    SSL:
    c := c+1;
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

