
-- http://groups.google.com/group/fa.haskell/browse_thread/thread/367f689a9606b275/9ab0090241a44c2b?lnk=st&q=haskell+school+of+expression+9.9&rnum=1#9ab0090241a44c2b

fix :: (a -> a) -> a
fix f = f (fix f)


remainder0 :: Integer -> Integer -> Integer
remainder0 a b = if a < b then a
                 else remainder0 (a - b) b

fix f = f (fix f)
remainder = fix rem_step
rem_step f a b = if a < b then a else f (a-b) b


{-

remainder 10 3 
 ==> fix rem_step 10 3
 ==> rem_step (fix rem_step) 10 3
 ==> if 10 < 3 then 10 else (fix rem_step) (10-3) 3
 ==> (fix rem_step) 7 3
 ==> fix rem_step 7 3
 ==> rem_step (fix rem_step) 7 3
 ==> if 7 < 3 then 7 else (fix rem_step) (7-3) 3
 ==> fix rem_step 4 3
 ==> rem_step (fix rem_step) 4 3
 ==> if 4 < 3 then 4 else (fix rem_step) (4-3) 3
 ==> fix rem_step 1 3
 ==> if 1 < 3 then 1 else (fix rem_step) (1-3) 3
 ==> 1

Huh!

-}
