------------------------ MODULE SequentialAlgoC -------------------------
EXTENDS TLC, Integers, Sequences

(*
--algorithm diehard

variables small = 0,
            big = 0;

define
    TypeOK == small \in 0..3 /\ big \in 0..5
    Res == big /= 4
end define;


process algo = "algo"
begin
    RepeatLabel:
        either  EmptySmall:
                    small := 0;
                    big := big;
                    goto RepeatLabel;
        or      EmptyBig:
                    big := 0;
                    small := small;
                    goto RepeatLabel;
        or      FillSmall:
                    small := 3;
                    big := big;
                    goto RepeatLabel;
        or      FillBig:
                    big := 5;
                    small := small;
                    goto RepeatLabel;
        or      FromSmallToBig:
                    if big + small <= 5 then
                        big := big + small;
                        small := 0;
                        goto RepeatLabel;
                    else
                        small := small - (5 - big);
                        big := 5;
                        goto RepeatLabel;
                    end if;
        or      FromBigToSmall:
                    if small + big <= 3 then
                        small := small + big;
                        big := 0;
                        goto RepeatLabel;
                    else
                        big := big - (3 - small);
                        small := 3;
                        goto RepeatLabel;
                    end if;
      end either;
end process;

end algorithm;
*)


==========================================================
