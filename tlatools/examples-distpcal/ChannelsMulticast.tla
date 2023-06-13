------------------------ MODULE ChannelsMulticast -------------------------
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

    process (pid = Id)
    {
smc: multicast(ch, [n \in Nodes |-> Id+n ] );
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
