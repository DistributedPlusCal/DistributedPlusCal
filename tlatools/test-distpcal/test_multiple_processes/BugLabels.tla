------------------------ MODULE BugLabels -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2;

process ( sid = 3 )
{
    L:
    c := c + 1;
}

process ( qid = 1 )
{
    R:
    c := c+1;
}
}
*)
================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"],
    "model-checking-args": {}
}
