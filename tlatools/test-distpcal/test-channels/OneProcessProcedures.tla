------------------------ MODULE OneProcessProcedures -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch, ch1[Nodes];

procedure sendToChannel(dest,mes)
{
	S:
	send(ch1[dest],mes);
	return;
}

procedure receiveFromChannel(dest)
variables rcv;
{
	R:
	receive(ch1[dest],rcv);
    cur := rcv;
	return;
}

process ( w \in Nodes )
variable cur = 1, loc = 0;
{
    Send:
    send(ch1[1],c+10+self);
    SendM:
    call sendToChannel(1,c+20+self);
    After:
    cur := cur + 1;
}
{
    Receive:
    receive(ch1[1],cur);
    ReceiveM:
    call receiveFromChannel(1);
    \* generate a deadlock to take a look at the trace
    receive(ch,cur);
}
}
*)
================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    }
}
