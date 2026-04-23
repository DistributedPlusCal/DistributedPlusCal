------------------------ MODULE ThreadsC -------------------------
EXTENDS Naturals, TLC, Sequences

(* PlusCal options (-distpcal) *)

(*--algorithm MyAlgo {
    variables
        tab = [ x \in 1..2 |-> 0 ];
    
    process (pid = 3)
    variables lv = 0;
    {
s1: lv := lv + 1;
    tab[1] := tab[1] + lv;
    }
    {
s2: lv := lv + 1;
    tab[2] := tab[2] + lv;
    }

    process (qid \in 1..2)
    variables t = 0;
    {
rc: await tab[self] > 0;
    t := tab[self];
ut: t := t + 1;
    }
}
*)
=============================================================================
