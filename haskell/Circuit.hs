{-
 | a dumb little circuit simulator in haskell
 | by tangentstorm, 2012/08/22
 |
 | This basically just calculates values using Ohm's law.
 | it (probably?) only works for simple circuits where there 
 | is a single path from the power source to each node, and
 | from each node back to the power source.
 |
 | many thanks to quicksilver and Axman6 on #haskell for advice
 |
 | license: http://unlicense.org/
 | ( in other words, do whatever you want with it... )
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- with the directive above, we can make our units typesafe
-- ref: http://necrobious.blogspot.com/2009/03/fun-example-of-haskells-newtype.html

import Control.Monad

newtype KOhms = KOhms Double deriving ( Num, Show, Eq, Fractional )
newtype MAmps = MAmps Double deriving ( Num, Show, Eq, Fractional )
newtype Volts = Volts Double deriving ( Num, Show, Eq )

type Indent = Int -- indentation for the result
type Str = String 

type Solve = ( Maybe KOhms, Maybe MAmps, Maybe Volts )
type Flow  = ( KOhms, MAmps, Volts )
data Cmpt  = I Str MAmps | R Str KOhms | Ser [ Cmpt ] | Par [ Cmpt ]

-- ohm's law(s)
-- we'll arbitrarily put the resistance to the left because
-- we happen to know resistance for the problem at hand
v :: KOhms -> MAmps -> Volts
i :: KOhms -> Volts -> MAmps
r :: MAmps -> Volts -> KOhms
v (KOhms r) (MAmps i) = Volts (r * i)
i (KOhms r) (Volts v) = MAmps (v / r)
r (MAmps i) (Volts v) = KOhms (v / i)


-- voltage for component c  = current i * resistance r of c
vc :: Cmpt -> MAmps -> Volts
vc c = v $ rc c


-- resistance is known or easy to calculate for all the components:
rc :: Cmpt -> KOhms
rc ( R _ ko ) = ko

-- not 100% sure about this one (resistance treated as 0 at the source?)
rc ( I _ _ )  = (KOhms 0) 

-- reisistance in series is just the sum:
rc ( Ser cs ) = sum [ rc c | c <- cs ] 

-- resistance in parallel is the reciprocal of the sum of the reciprocals
rc ( Par cs ) = 1.0 / sum [ 1.0 / rc c | c <- cs ]

-- current : 
ic :: Cmpt -> Flow -> MAmps
ic ( I _ i ) flo = i


-- display stuff:

shoFlow :: Flow  -> Str
shoFlow (ko, ma, v) = "( " ++ (show ko) ++ ", " ++ (show ma) ++ ", " ++ (show v) ++ " )"

labelFor :: Cmpt -> Str
labelFor ( I lbl _ ) = lbl
labelFor ( R lbl _ ) = lbl
labelFor ( Par _ )   = "Par"
labelFor ( Ser _ )   = "Ser"

indent :: Int -> IO ()
indent i = putStr (replicate i ' ')

-- walk the tree recursively
walk :: Cmpt -> Indent -> Flow -> IO ()
walk c ind flo
      = do indent ind
           putStrLn ( "-> " ++ ( labelFor c ) ++ " " ++ ( shoFlow flo ))
           case c of
             Par cs    -> do { mapM doPar cs ; return () }
             Ser cs    -> do { foldM doSer flo cs ; return () }
             otherwise -> return ()
           indent ind
           putStrLn ( "<- " ++ ( labelFor c ) ++ " " ++ ( shoFlow flo' ))
        where
           flo' = throughput c flo
           doPar = \c' -> walk c' ( ind + 3 ) flo
           doSer = \f0 c' -> do { walk c' ( ind + 3 ) f0 ; return ( throughput c f0 ) }


-- throughput is my naive word for the result of current passing through the component: 
-- TODO : actually calculate the throughput! :)
throughput :: Cmpt -> Flow -> Flow
throughput c flo@(o, a, v) = flo


unknown :: Maybe a
unknown = Nothing

-- circuit at : http://imgur.com/ZSDAf
circuit = Par [ Ser [ r2, r1 ], r3, r4 ]

r1 = R "r1" (KOhms  3.0)
r2 = R "r2" (KOhms  1.0)
r3 = R "r3" (KOhms  5.0)
r4 = R "r4" (KOhms 20.0)

i0 = I "i0" (MAmps 10.0)
amps ( I _ i ) = i

-- main
main = walk circuit 0 (0, amperage, voltage)
  where amperage = amps i0
        voltage  = vc circuit amperage


{--  OUTPUT FOR THIS VERSION:

*Main Control.Monad> :load Circuit.hs
[1 of 1] Compiling Main             ( Circuit.hs, interpreted )
Ok, modules loaded: Main.
*Main Control.Monad> main
-> Par ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
   -> Ser ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
      -> r2 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
      <- r2 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
      -> r1 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
      <- r1 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
   <- Ser ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
   -> r3 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
   <- r3 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
   -> r4 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
   <- r4 ( KOhms 0.0, MAmps 10.0, Volts 20.0 )
<- Par ( KOhms 0.0, MAmps 10.0, Volts 20.0 )

--}
