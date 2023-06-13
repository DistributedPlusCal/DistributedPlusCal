------------------------ MODULE ChannelsC -------------------------
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
s1: send(ch[1],Id+1);
    }
    {
s2: send(ch[2],Id+2);
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
