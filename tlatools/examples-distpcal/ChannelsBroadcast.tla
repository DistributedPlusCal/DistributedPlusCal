------------------------ MODULE ChannelsBroadcast -------------------------
EXTENDS Naturals, TLC, Sequences, Bags

(* PlusCal options (-distpcal) *)

(*--algorithm MyAlgo {
    variables s = 0;
    \* fifos
    channels 
    ch[Nodes];
    
    define {
        Nodes == 1..2
        Id == 3
    }

    macro broadcast(chan,m)
    {
        multicast(chan,[ag \in DOMAIN chan |-> m]);
    }

    process (pid = Id)
    {
sbc: broadcast(ch, Id);
    }

    process (qid \in Nodes)
    variables t = 0;
    {
rcv: receive(ch[self],t);
add: s := s + t;
    }
}
*)
=============================================================================
