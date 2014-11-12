{-# language GADTs, StandaloneDeriving, FlexibleInstances #-}
{- proof language prototype -}
import Control.Applicative
import Data.Function (on)
import Data.HashMap


{- AST -}
data Bit = Boolean; type XNum = X Float
type Var = String; type Err = String; type Lbl = String;
type Step = String; type Proof = [Step]
data X a where
    F :: X Bit; T :: X Bit; Err :: X Err  -- false, true, error
    -- boolean functions ---
    Not :: X Bit -> X Bit                 -- logical 'not'
    (:∧) :: X Bit -> X Bit -> X Bit       -- logical and
    (:∨) :: X Bit -> X Bit -> X Bit       -- logical or
    (:→) :: X a -> X a -> X Bit           -- implies
    (:←) :: X a -> X b -> X Bit           -- refines
    (:=) :: X a -> X a -> X Bit           -- equal
    (:≠) :: X a -> X a -> X Bit           -- not equal
    -- proof-carrying-code
    Eql :: X a -> X a -> Proof -> X Bit   -- equality proof
    Rfn :: X a -> X a -> Proof -> X Bit   -- refinement proof
    Imp :: X a -> X a -> Proof -> X Bit   -- implication proof
    -- numbers
    N  :: Float -> XNum
    (:+) :: XNum -> XNum -> XNum          -- addition
    (:-) :: XNum -> XNum -> XNum          -- subtraction
    (:^) :: XNum -> XNum -> XNum          -- exponent
    (:*) :: XNum -> XNum -> XNum          -- multiplication
    (:%) :: XNum -> XNum -> XNum          -- division
    -- programs --
    (:.):: X a -> X a                     -- dependent composition (sequence)
    (:!):: Lbl -> X a -> X a
    I  :: Lbl  -> X a                     -- invoke a label
    G  :: X a                             -- grouped expr (in parens)
    V  :: Var -> X Var                    -- variable
    L  :: [X a] -> X a                    -- List
    IF :: X a -> X b -> X b               -- if/then/else
    C  :: Char -> X Char                  -- Char
    Bun :: [X a] -> X a                   -- bundle
    Set :: [X a] -> X a                   -- Set
    (:..) :: X a -> X a -> X [a]          -- Range

deriving instance Show (X a)



{- Semantics -}

-- number theory --
instance Num (X Float) where
    (N x) + (N y) = N (x + y)
    (N x) * (N y) = N (x * y)
    abs (N y) = N (abs y)
    signum (N y) = N (signum y)
    negate (N y) = N (negate y)
    fromInteger y = N (fromInteger y)



-- booleans --

bool :: X Bit -> Bool; bool T = True; bool F = False
tbit :: Bool -> X Bit; tbit True = T; tbit False = F

x <: y = if x then y else True -- ≤ = → (implication)
x >: y = if y then x else True -- ≥ = ← (refinement)

dybit :: (Bool -> Bool -> Bool) -> X Bit -> X Bit -> X Bit
dybit op x y = tbit $ ((bool$eval x) `op` (bool$eval y))


{- prove: ((x :^ y ):^ z) :<--> ((x :^ z) :^ y)
   ((x :^ y) :^ z) -- starting expr
 = (x :^ (y :* z)) -- exponent rule
 = (x :^ (z :* y)) -- commutative rule for *
 = ((x :^ z) :^ y) -- exponent rule
 qed -}

-- general evaluator --

eval :: X a -> X a
eval (x :∨ y) = dybit (||) x y
eval (x :∧ y) = dybit (&&) x y
eval (Rfn x y p) = T
eval (Imp x y p) = T
eval (Eql x y p) = T
eval (N 0) = N 3
eval ex = ex

x +. y = eval (x :∨ y)
x *. y = eval (x :∧ y)

o = F
l = T



a .$ b = take a $ repeat b
main = putStrLn.show $ o +. l
