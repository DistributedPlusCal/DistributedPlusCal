------------------------ MODULE BugLabels -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-label -distpcal) *)

(*--algorithm dummy  {
variables c = 2;

procedure f(x)
variable lv = 0;
{
    A:
        c := c + x + 1;
        return;
}

process ( sid = 3 )
{
    L:
    c := c + 1;
    call f(1);
}

process ( qid = 1 )
{
    c := c + 1;
    call f(2);
}
{
    c := c + 2;
    call f(3);
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
