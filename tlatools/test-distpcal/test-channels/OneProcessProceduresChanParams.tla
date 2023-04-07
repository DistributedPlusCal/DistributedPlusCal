------------------------ MODULE OneProcessProceduresChanParams -------------------------
EXTENDS TLC, Integers, Sequences

Nodes == 1..2

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2, r = 22;
channels ch, ch1[Nodes];

\* shouldn't use chan as a parameter
procedure sendToChannel(chanS,mes)
{
	send(chanS,mes);
	return;
}

\* shouldn't use chan as a parameter
procedure receiveFromChannel(chanR)
variables rcv;
{
	receive(chanR,rcv);
	return;
}

\* shouldn't use mes as a parameter
procedure receiveFromChannelInParam(mes)
{
	receive(ch,mes);
	return;
}

process ( w \in Nodes )
variable cur = 1, loc = 0;
{
    cur := cur + 1;
}
}
*)
================================================
{
    "need-error-parse": true,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {
        "defaultInitValue": 0
    }
}
