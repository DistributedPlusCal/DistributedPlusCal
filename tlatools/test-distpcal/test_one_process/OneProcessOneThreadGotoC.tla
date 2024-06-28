----- MODULE OneProcessOneThreadGotoC----

(*--algorithm X {
variables 
    found = FALSE
    process (x \in {})
    {
a:      goto a;
    }
}*)
=============================================================================
{
    "need-error-parse": false,
    "need-error-check": false,
    "args-check": ["-deadlock"]
}
