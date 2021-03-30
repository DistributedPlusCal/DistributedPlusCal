------------------------ MODULE SequentialAlgoC -------------------------
EXTENDS TLC, Integers, Sequences

(*
--algorithm dieHard {
	
variables small = 0, big = 0;
    {
        while (TRUE) {
            either 
                    big := 5 \* Fill big
            or
                    small := 3 \* Fill small
            or
                    big := 0 \* empty big
            or
                    small := 0 \* empty small
            or
                    with (poured = Min(big+small, 5) - big) { \* from big to small
                        big := big + poured;
                        small := small - poured;
                    }
            or
                    with (poured = Min(big+small, 3)) { \* from small to big
                        big := big - poured;
                        small := small + poured;
                    }   
        }
        
    }

}
*)

==========================================================
