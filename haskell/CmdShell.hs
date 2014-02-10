---
--- This was an attempt to create a monad that
--- would allow implicit function composition.
--- 
--- I couldn't get it working, though.
--- I think maybe the problem is that I was trying
--- to make a TCmd monad instead of a TStack monad.
---
--- Perhaps I will revisit this when my haskell skills
--- are stronger.
---
{-# OPTIONS  -XGADTs -XTypeSynonymInstances -XInstanceSigs -XRankNTypes #-}
module Main where
import Control.Monad

-- Here is the code I want to run:

demo :: TCmd (demo)
Int = do { lit 3; lit 2; lit 1; add; mul }

main :: IO ()
main = do
  if run demo == [(1+2)*3]
    then putStrLn "ok"
    else putStrLn "failed. :("

-- The idea is that these commands are passing
-- around an implicit stack.
data TCmd a = Cmd (TStack a -> TStack a)
  
-- Stacks are just lists, but we will wrap them
-- in a special type to show that we're using
-- them in a specific way.
newtype TStack a = S [a]
  deriving (Eq, Show)

-- First, we will implement the instructions as simple functions
-- that operate on lists. Lets call them "Ops":
type Op a = [a] -> [a]

-- opLit produces an Op that pushes a specific value onto the stack.
opLit :: a -> Op a
opLit x = \xs -> x:xs

-- opAdd and opMul perform simple arithmetic:
opAdd :: Num a => Op a
opAdd = \(x:y:zs) -> (x+y):zs

opMul :: Num a => Op a
opMul = \(x:y:zs) -> (x*y):zs

-- opNop does nothing (not used above, but for experimentation):
opNop :: Op a
opNop = \xs -> xs

-- Since we don't want to pass the stack explicitly, we want
-- a way to convert these operations into TCmd instances.
--
-- The following function does this work for us:
cmd :: Op a -> TCmd a
cmd op = Cmd $ \(S xs)  -> S (op xs)

-- and so:
lit :: a -> TCmd a
lit x = cmd (opLit x)

add :: Num a => TCmd a
add   = cmd (opAdd)

mul :: Num a => TCmd a
mul = cmd (opMul)

nop :: TCmd a
nop = cmd (opNop)


-- To extract the topmost value:
pop :: TStack a -> a
pop (S xs) = head xs

-- Now, in order for the code to work, we have to make
-- TCmd into a Monad:
instance Monad TCmd where
  
  -- This should create a TCmd that constructs a brand new
  -- stack with only the given value on it.
  return :: a -> TCmd a
  return x = Cmd $ \_ -> S [x]

  -- (>>=)  :: m a -> (a -> m b) -> m b
  -- This is the trickiest part.
  -- We want to take a TCmd and a function that *creates* a TCmd
  -- and produce a new TCmd.
  (>>=)  :: forall a b. TCmd a -> (a -> TCmd b) -> TCmd b
  c >>= g = nop -- Cmd $ \s -> S (result g (result c s))

-- finally, `run` creates a new stack, lets the Cmd do its work,
-- and then extracts the underlying list from the resulting TStack.
run :: TCmd a -> [a]
run c = result c (S [])

result :: TCmd a -> TStack a -> [a]
result (Cmd c) s = r where (S r) = c s
