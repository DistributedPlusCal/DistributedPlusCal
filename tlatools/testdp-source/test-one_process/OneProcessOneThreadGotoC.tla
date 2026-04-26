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
    "expect-error-parse": false,
    "expect-error-check": false,
    "args-check": ["-deadlock"],
    "compare_to": ""
}
